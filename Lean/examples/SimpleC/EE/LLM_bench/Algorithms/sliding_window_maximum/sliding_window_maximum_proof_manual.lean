import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_goal
import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_proof_auto

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open sliding_window_maximum_goal sliding_window_maximum_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem aux_maxSlidingWindow_entail_wit_2_split_goal_2 : (forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) := by

  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  refine ⟨PreH21.1, PreH21.2.1, PreH21.2.2.1, ?_⟩
  intro idx hidx hw
  exact PreH21.2.2.2.1 idx hidx (by omega)

theorem aux_maxSlidingWindow_entail_wit_3_split_goal_1 : (forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueueDropLoopState l q_l_2 (head + 1) tail i k_pre)) := by

  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact drop_loop_remove_expired_head__head_drop_transitions l q_l_2 head tail i k_pre PreH2 PreH1 PreH21

theorem aux_maxSlidingWindow_entail_wit_6_split_goal_1 : (forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueuePendingState l q_l_2 head (tail - 1) i k_pre)) := by

  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact SWMQueuePendingState_drop_tail__pending_and_tail_drop l q_l_2 head tail i k_pre PreH2 PreH1 PreH21

theorem aux_maxSlidingWindow_entail_wit_8_split_goal_2 : (forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))))) ,
  (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1) (i + 1) k_pre)) := by

  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact queue_append_state__value_loop_exit_and_append l q_l_2 head tail i k_pre
    (by omega) PreH1 (by omega) ⟨PreH8, PreH9⟩ PreH10 PreH19 PreH22

theorem aux_maxSlidingWindow_entail_wit_8_split_goal_4 : (forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))))) ,
  ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre)) := by

  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [Zlength_replace_Znth]; exact PreH5

theorem aux_maxSlidingWindow_entail_wit_9_split_goal_1 : (forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i >= (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) := by

  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have h := PreH20.2.2.2.2 (show head < tail ∧ k_pre ≤ i+1 by omega)
  rw [show i-k_pre+1 = i+1-k_pre by omega]
  exact h

theorem aux_maxSlidingWindow_entail_wit_10_split_goal_2 : (forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l_2 (0 : Int)))) (PreH13 : ((Znth head q_l_2 (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH23 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) ,
  (SWMOutputPrefix l k_pre (((i - k_pre) + 1) + 1) (out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int))))) := by

  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  rw [← PreH14]
  apply SWMOutputPrefix_app_single__window_output_append l k_pre out_idx out_l_2 _ PreH18 PreH19
  rw [PreH14, show i-k_pre+1+k_pre = i+1 by omega]
  exact PreH23

attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

theorem proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1 := by
  unfold maxSlidingWindow_entail_wit_1
  right
  intro l n k hk hkn hn hl hb hu
  split_pure_spatial
  · sep_apply (naive_C_Rules.IntArray.undef_full_split_to_undef_seg (&("q")) n 100000 (by omega))
    cancel
  · dump_pre_spatial
    rfl

theorem proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2 := by
  unfold maxSlidingWindow_entail_wit_2
  right
  intro l n k q z hz hk hkn hn hl hb hu hz0 hzn hq
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    simp only [Zlength_app, Zlength_cons, Zlength_nil, hq]
    omega

theorem proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3 := by
  unfold maxSlidingWindow_entail_wit_3
  right
  intro l n k q z hz hk hkn hn hl hb hu hz0 hzn hq
  have hqueue : SWMQueueState l q 0 0 0 k := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro pos hp; omega
    · intro a b hab; omega
    · intro a b hab; omega
    · intro idx hi hw; omega
    · intro hh; omega
  have hout : SWMOutputPrefix l k 0 [] := by intro idx hi; omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | simp [Zlength_nil, sublist_same]
      | exact hqueue
      | exact hout
      | simp [sublist, Forall.iff_forall_mem]
private theorem indexed_Forall {A : Type} (P : A → Prop) (l : List A) (d : A) :
    Forall P l ↔ ∀ i, 0 ≤ i ∧ i < Zlength l → P (Znth i l d) := by
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

private theorem forall_sublist_index {A : Type} (P : A → Prop) (d : A)
    (l : List A) (lo hi : Int) (hb : 0 ≤ lo ∧ lo ≤ hi) (he : hi ≤ Zlength l) :
    Forall P (sublist lo hi l) ↔ ∀ k, lo ≤ k ∧ k < hi → P (Znth k l d) := by
  rw [indexed_Forall P _ d]
  have hlen : Zlength (sublist lo hi l) = hi-lo := by
    unfold Zlength
    rw [sublist_length lo hi l hb he]
    exact Int.toNat_of_nonneg (by omega)
  constructor
  · intro h k hk
    have hh := h (k-lo) (by rw [hlen]; omega)
    rw [Znth_sublist d lo (k-lo) hi l hb.1 (by omega), Int.sub_add_cancel] at hh
    exact hh
  · intro h j hj
    rw [hlen] at hj
    rw [Znth_sublist d lo j hi l hb.1 hj]
    exact h (j+lo) (by omega)


theorem proof_of_maxSlidingWindow_entail_wit_4_split_goal_1 : maxSlidingWindow_entail_wit_4_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_4_split_goal_1
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH17_indexed := (indexed_Forall ((LE.le (α := Int)) ((-10000))) l (0 : Int)).mp PreH17
  have PreH18_indexed := (indexed_Forall ((GE.ge (α := Int)) (10000)) l (0 : Int)).mp PreH18
  have hs : SWMQueueStorageSafe l q_l_2 head tail i := by
    refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
    intro pos hp
    have hlower := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22 pos hp
    have hupper := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23 pos hp
    exact ⟨hlower, by omega⟩
  have hshape : SWMOutputPrefixShape l k_pre out_idx out_l_2 := by
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
  have hin : SWMInputSafe l n_pre k_pre := by
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    intro idx hidx
    exact ⟨PreH17_indexed idx (by omega), PreH18_indexed idx (by omega)⟩
  have hbounds : ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q_l_2 0 ∧ Znth pos q_l_2 0 < n_pre := by
    intro pos hp
    have hh := hs.2.2.2.2 pos hp
    constructor
    · exact hh.1
    · omega
  apply aux_maxSlidingWindow_entail_wit_2_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2
  all_goals first | assumption | omega | exact hs | exact hshape | exact hin | exact hbounds

theorem proof_of_maxSlidingWindow_entail_wit_5_split_goal_3 : maxSlidingWindow_entail_wit_5_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_5_split_goal_3
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH17_indexed := (indexed_Forall ((LE.le (α := Int)) ((-10000))) l (0 : Int)).mp PreH17
  have PreH18_indexed := (indexed_Forall ((GE.ge (α := Int)) (10000)) l (0 : Int)).mp PreH18
  have hs : SWMQueueStorageSafe l q_l_2 head tail i := by
    refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
    intro pos hp
    have hlower := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22 pos hp
    have hupper := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23 pos hp
    exact ⟨hlower, by omega⟩
  have hshape : SWMOutputPrefixShape l k_pre out_idx out_l_2 := by
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
  have hin : SWMInputSafe l n_pre k_pre := by
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    intro idx hidx
    exact ⟨PreH17_indexed idx (by omega), PreH18_indexed idx (by omega)⟩
  have hbounds : ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q_l_2 0 ∧ Znth pos q_l_2 0 < n_pre := by
    intro pos hp
    have hh := hs.2.2.2.2 pos hp
    constructor
    · exact hh.1
    · omega
  apply aux_maxSlidingWindow_entail_wit_3_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2
  all_goals first | assumption | omega | exact hs | exact hshape | exact hin | exact hbounds

theorem proof_of_maxSlidingWindow_entail_wit_7_split_goal_4 : maxSlidingWindow_entail_wit_7_split_goal_4 := by
  unfold maxSlidingWindow_entail_wit_7_split_goal_4
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have PreH17_indexed := (indexed_Forall ((LE.le (α := Int)) ((-10000))) l (0 : Int)).mp PreH17
  have PreH18_indexed := (indexed_Forall ((GE.ge (α := Int)) (10000)) l (0 : Int)).mp PreH18
  have hs : SWMQueueStorageSafe l q_l_2 head tail i := by
    refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
    intro pos hp
    have hlower := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22 pos hp
    have hupper := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23 pos hp
    exact ⟨hlower, by omega⟩
  have hshape : SWMOutputPrefixShape l k_pre out_idx out_l_2 := by
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
  have hin : SWMInputSafe l n_pre k_pre := by
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    intro idx hidx
    exact ⟨PreH17_indexed idx (by omega), PreH18_indexed idx (by omega)⟩
  have hbounds : ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q_l_2 0 ∧ Znth pos q_l_2 0 < n_pre := by
    intro pos hp
    have hh := hs.2.2.2.2 pos hp
    constructor
    · exact hh.1
    · omega
  apply aux_maxSlidingWindow_entail_wit_6_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2
  all_goals first | assumption | omega | exact hs | exact hshape | exact hin | exact hbounds

theorem proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_3 : maxSlidingWindow_entail_wit_8_1_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_8_1_split_goal_3
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH16_indexed := (indexed_Forall ((LE.le (α := Int)) ((-10000))) l (0 : Int)).mp PreH16
  have PreH17_indexed := (indexed_Forall ((GE.ge (α := Int)) (10000)) l (0 : Int)).mp PreH17
  have hs : SWMQueueStorageSafe l q_l_2 head tail i := by
    refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
    intro pos hp
    have hlower := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH21 pos hp
    have hupper := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22 pos hp
    exact ⟨hlower, by omega⟩
  have hshape : SWMOutputPrefixShape l k_pre out_idx out_l_2 := by
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
  have hin : SWMInputSafe l n_pre k_pre := by
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    intro idx hidx
    exact ⟨PreH16_indexed idx (by omega), PreH17_indexed idx (by omega)⟩
  have hbounds : ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q_l_2 0 ∧ Znth pos q_l_2 0 < n_pre := by
    intro pos hp
    have hh := hs.2.2.2.2 pos hp
    constructor
    · exact hh.1
    · omega
  apply aux_maxSlidingWindow_entail_wit_8_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx
  all_goals first | assumption | omega | exact hs | exact hshape | exact hin | exact hbounds

theorem proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_3 : maxSlidingWindow_entail_wit_8_2_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_8_2_split_goal_3
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have PreH17_indexed := (indexed_Forall ((LE.le (α := Int)) ((-10000))) l (0 : Int)).mp PreH17
  have PreH18_indexed := (indexed_Forall ((GE.ge (α := Int)) (10000)) l (0 : Int)).mp PreH18
  have hs : SWMQueueStorageSafe l q_l_2 head tail i := by
    refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
    intro pos hp
    have hlower := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22 pos hp
    have hupper := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23 pos hp
    exact ⟨hlower, by omega⟩
  have hshape : SWMOutputPrefixShape l k_pre out_idx out_l_2 := by
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
  have hin : SWMInputSafe l n_pre k_pre := by
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    intro idx hidx
    exact ⟨PreH17_indexed idx (by omega), PreH18_indexed idx (by omega)⟩
  have hbounds : ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q_l_2 0 ∧ Znth pos q_l_2 0 < n_pre := by
    intro pos hp
    have hh := hs.2.2.2.2 pos hp
    constructor
    · exact hh.1
    · omega
  apply aux_maxSlidingWindow_entail_wit_8_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx
  all_goals first | assumption | omega | exact hs | exact hshape | exact hin | exact hbounds

theorem proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_4 : maxSlidingWindow_entail_wit_8_1_split_goal_4 := by
  unfold maxSlidingWindow_entail_wit_8_1_split_goal_4
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH16_indexed := (indexed_Forall ((LE.le (α := Int)) ((-10000))) l (0 : Int)).mp PreH16
  have PreH17_indexed := (indexed_Forall ((GE.ge (α := Int)) (10000)) l (0 : Int)).mp PreH17
  have hs : SWMQueueStorageSafe l q_l_2 head tail i := by
    refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
    intro pos hp
    have hlower := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH21 pos hp
    have hupper := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22 pos hp
    exact ⟨hlower, by omega⟩
  have hshape : SWMOutputPrefixShape l k_pre out_idx out_l_2 := by
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
  have hin : SWMInputSafe l n_pre k_pre := by
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    intro idx hidx
    exact ⟨PreH16_indexed idx (by omega), PreH17_indexed idx (by omega)⟩
  have hbounds : ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q_l_2 0 ∧ Znth pos q_l_2 0 < n_pre := by
    intro pos hp
    have hh := hs.2.2.2.2 pos hp
    constructor
    · exact hh.1
    · omega
  apply aux_maxSlidingWindow_entail_wit_8_split_goal_4 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx
  all_goals first | assumption | omega | exact hs | exact hshape | exact hin | exact hbounds

theorem proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_4 : maxSlidingWindow_entail_wit_8_2_split_goal_4 := by
  unfold maxSlidingWindow_entail_wit_8_2_split_goal_4
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have PreH17_indexed := (indexed_Forall ((LE.le (α := Int)) ((-10000))) l (0 : Int)).mp PreH17
  have PreH18_indexed := (indexed_Forall ((GE.ge (α := Int)) (10000)) l (0 : Int)).mp PreH18
  have hs : SWMQueueStorageSafe l q_l_2 head tail i := by
    refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
    intro pos hp
    have hlower := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22 pos hp
    have hupper := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23 pos hp
    exact ⟨hlower, by omega⟩
  have hshape : SWMOutputPrefixShape l k_pre out_idx out_l_2 := by
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
  have hin : SWMInputSafe l n_pre k_pre := by
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    intro idx hidx
    exact ⟨PreH17_indexed idx (by omega), PreH18_indexed idx (by omega)⟩
  have hbounds : ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q_l_2 0 ∧ Znth pos q_l_2 0 < n_pre := by
    intro pos hp
    have hh := hs.2.2.2.2 pos hp
    constructor
    · exact hh.1
    · omega
  apply aux_maxSlidingWindow_entail_wit_8_split_goal_4 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx
  all_goals first | assumption | omega | exact hs | exact hshape | exact hin | exact hbounds

theorem proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 : maxSlidingWindow_entail_wit_9_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_9_split_goal_1
  intro l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have PreH16_indexed := (indexed_Forall ((LE.le (α := Int)) ((-10000))) l (0 : Int)).mp PreH16
  have PreH17_indexed := (indexed_Forall ((GE.ge (α := Int)) (10000)) l (0 : Int)).mp PreH17
  have hs : SWMQueueStorageSafe l q_l_2 head tail (i+1) := by
    refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
    intro pos hp
    have hlower := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH21 pos hp
    have hupper := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22 pos hp
    exact ⟨hlower, by omega⟩
  have hshape : SWMOutputPrefixShape l k_pre out_idx out_l_2 := by
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
  have hin : SWMInputSafe l n_pre k_pre := by
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    intro idx hidx
    exact ⟨PreH16_indexed idx (by omega), PreH17_indexed idx (by omega)⟩
  have hbounds : ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q_l_2 0 ∧ Znth pos q_l_2 0 < n_pre := by
    intro pos hp
    have hh := hs.2.2.2.2 pos hp
    constructor
    · exact hh.1
    · omega
  apply aux_maxSlidingWindow_entail_wit_9_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx
  all_goals first | assumption | omega | exact hs | exact hshape | exact hin | exact hbounds

theorem proof_of_maxSlidingWindow_entail_wit_10_1_split_goal_1 : maxSlidingWindow_entail_wit_10_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_10_1_split_goal_1
  intro l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have PreH17_indexed := (indexed_Forall ((LE.le (α := Int)) ((-10000))) l (0 : Int)).mp PreH17
  have PreH18_indexed := (indexed_Forall ((GE.ge (α := Int)) (10000)) l (0 : Int)).mp PreH18
  have hs : SWMQueueStorageSafe l q_l_2 head tail (i+1) := by
    refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
    intro pos hp
    have hlower := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22 pos hp
    have hupper := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23 pos hp
    exact ⟨hlower, by omega⟩
  have hshape : SWMOutputPrefixShape l k_pre out_idx out_l_2 := by
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
  have hin : SWMInputSafe l n_pre k_pre := by
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    intro idx hidx
    exact ⟨PreH17_indexed idx (by omega), PreH18_indexed idx (by omega)⟩
  have hbounds : ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q_l_2 0 ∧ Znth pos q_l_2 0 < n_pre := by
    intro pos hp
    have hh := hs.2.2.2.2 pos hp
    constructor
    · exact hh.1
    · omega
  apply aux_maxSlidingWindow_entail_wit_10_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx
  all_goals first | assumption | omega | exact hs | exact hshape | exact hin | exact hbounds

private theorem after_drop_pending (l q : List Int) (h t i k : Int)
    (hs : SWMQueueAfterDrop l q h t i k) : SWMQueuePendingState l q h t i k := by
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩
  intro idx hi hw
  exact Or.inl (hs.2.2.2 idx hi hw)

theorem proof_of_maxSlidingWindow_entail_wit_2_split_goal_1 : maxSlidingWindow_entail_wit_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_2_split_goal_1
  intro l n_pre k_pre q_init_2 z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  simp only [Zlength_app, Zlength_cons, Zlength_nil]
  omega

theorem proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 : maxSlidingWindow_entail_wit_5_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_5_split_goal_1
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23
  apply (forall_sublist_index _ 0 q_l_2 (head+1) tail (by omega) (by omega)).mpr
  intro pos hp
  exact hhi pos (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 : maxSlidingWindow_entail_wit_5_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_5_split_goal_2
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23
  apply (forall_sublist_index _ 0 q_l_2 (head+1) tail (by omega) (by omega)).mpr
  intro pos hp
  exact hlo pos (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_6_1_split_goal_1 : maxSlidingWindow_entail_wit_6_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_6_1_split_goal_1
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH21
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  rcases PreH20 with ⟨he, hi, hv, hc⟩
  refine ⟨?_, hi, hv, ?_⟩
  · intro pos hp; omega
  · intro idx hi hw
    exact Or.inl (hc idx hi hw)

theorem proof_of_maxSlidingWindow_entail_wit_6_2_split_goal_1 : maxSlidingWindow_entail_wit_6_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_6_2_split_goal_1
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23
  intro hh
  have hlower := hlo (tail-1) (by omega)
  have hupper := hhi (tail-1) (by omega)
  refine ⟨⟨⟨by omega, by omega⟩, hlower⟩, hupper⟩

theorem proof_of_maxSlidingWindow_entail_wit_6_2_split_goal_2 : maxSlidingWindow_entail_wit_6_2_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_6_2_split_goal_2
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23
  apply after_drop_pending
  exact drop_loop_exit_nonexpired__head_drop_transitions l q_l_2 head tail i k_pre (by omega) (by omega) PreH21

theorem proof_of_maxSlidingWindow_entail_wit_7_split_goal_1 : maxSlidingWindow_entail_wit_7_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_7_split_goal_1
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23
  intro hh
  have hlower := hlo (tail-1-1) (by omega)
  have hupper := hhi (tail-1-1) (by omega)
  refine ⟨⟨⟨by omega, by omega⟩, hlower⟩, hupper⟩

theorem proof_of_maxSlidingWindow_entail_wit_7_split_goal_2 : maxSlidingWindow_entail_wit_7_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_7_split_goal_2
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23
  apply (forall_sublist_index _ 0 q_l_2 head (tail-1) (by omega) (by omega)).mpr
  intro pos hp
  exact hhi pos (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_7_split_goal_3 : maxSlidingWindow_entail_wit_7_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_7_split_goal_3
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23
  apply (forall_sublist_index _ 0 q_l_2 head (tail-1) (by omega) (by omega)).mpr
  intro pos hp
  exact hlo pos (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_1 : maxSlidingWindow_entail_wit_8_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_8_1_split_goal_1
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH21
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  apply (forall_sublist_index _ 0 (replace_Znth tail i q_l_2) head (tail+1) (by omega) (by simpa only [Zlength_replace_Znth] using (show tail+1 ≤ Zlength q_l_2 by omega))).mpr
  intro pos hp
  have hb := replace_Znth_append_bounds__value_loop_exit_and_append q_l_2 head tail i n_pre (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by intro j hj; exact ⟨hlo j hj, hhi j hj⟩) pos hp
  exact hb.2

theorem proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_2 : maxSlidingWindow_entail_wit_8_1_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_8_1_split_goal_2
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH21
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  apply (forall_sublist_index _ 0 (replace_Znth tail i q_l_2) head (tail+1) (by omega) (by simpa only [Zlength_replace_Znth] using (show tail+1 ≤ Zlength q_l_2 by omega))).mpr
  intro pos hp
  have hb := replace_Znth_append_bounds__value_loop_exit_and_append q_l_2 head tail i n_pre (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by intro j hj; exact ⟨hlo j hj, hhi j hj⟩) pos hp
  exact hb.1

theorem proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_1 : maxSlidingWindow_entail_wit_8_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_8_2_split_goal_1
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23
  apply (forall_sublist_index _ 0 (replace_Znth tail i q_l_2) head (tail+1) (by omega) (by simpa only [Zlength_replace_Znth] using (show tail+1 ≤ Zlength q_l_2 by omega))).mpr
  intro pos hp
  have hb := replace_Znth_append_bounds__value_loop_exit_and_append q_l_2 head tail i n_pre (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by intro j hj; exact ⟨hlo j hj, hhi j hj⟩) pos hp
  exact hb.2

theorem proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_2 : maxSlidingWindow_entail_wit_8_2_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_8_2_split_goal_2
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23
  apply (forall_sublist_index _ 0 (replace_Znth tail i q_l_2) head (tail+1) (by omega) (by simpa only [Zlength_replace_Znth] using (show tail+1 ≤ Zlength q_l_2 by omega))).mpr
  intro pos hp
  have hb := replace_Znth_append_bounds__value_loop_exit_and_append q_l_2 head tail i n_pre (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by intro j hj; exact ⟨hlo j hj, hhi j hj⟩) pos hp
  exact hb.1

theorem proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 : maxSlidingWindow_entail_wit_9_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_9_split_goal_2
  intro l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH21
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  exact hhi head (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_9_split_goal_3 : maxSlidingWindow_entail_wit_9_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_9_split_goal_3
  intro l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH21
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  exact hlo head (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_10_1_split_goal_2 : maxSlidingWindow_entail_wit_10_1_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_10_1_split_goal_2
  intro l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hlo := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH22
  have hhi := (forall_sublist_index _ 0 q_l_2 head tail (by omega) (by omega)).mp PreH23
  simp only [Zlength_app, Zlength_cons, Zlength_nil]
  omega

theorem proof_of_maxSlidingWindow_entail_wit_4 : maxSlidingWindow_entail_wit_4 := by
  unfold maxSlidingWindow_entail_wit_4
  right
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_4_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_maxSlidingWindow_entail_wit_4_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | assumption
    | omega
    | trivial

theorem proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5 := by
  unfold maxSlidingWindow_entail_wit_5
  right
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_5_split_goal_3 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_maxSlidingWindow_entail_wit_5_split_goal_3 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | assumption
    | omega
    | trivial

theorem proof_of_maxSlidingWindow_entail_wit_6_1 : maxSlidingWindow_entail_wit_6_1 := by
  unfold maxSlidingWindow_entail_wit_6_1
  right
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_6_1_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | exact (proof_of_maxSlidingWindow_entail_wit_6_1_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | assumption
    | omega
    | trivial

theorem proof_of_maxSlidingWindow_entail_wit_6_2 : maxSlidingWindow_entail_wit_6_2 := by
  unfold maxSlidingWindow_entail_wit_6_2
  right
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_6_2_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_maxSlidingWindow_entail_wit_6_2_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_6_2_split_goal_2 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_maxSlidingWindow_entail_wit_6_2_split_goal_2 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | assumption
    | omega
    | trivial

theorem proof_of_maxSlidingWindow_entail_wit_7 : maxSlidingWindow_entail_wit_7 := by
  unfold maxSlidingWindow_entail_wit_7
  right
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_7_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | exact (proof_of_maxSlidingWindow_entail_wit_7_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_7_split_goal_2 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | exact (proof_of_maxSlidingWindow_entail_wit_7_split_goal_2 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_7_split_goal_3 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | exact (proof_of_maxSlidingWindow_entail_wit_7_split_goal_3 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_7_split_goal_4 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | exact (proof_of_maxSlidingWindow_entail_wit_7_split_goal_4 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | assumption
    | omega
    | trivial

theorem proof_of_maxSlidingWindow_entail_wit_8_1 : maxSlidingWindow_entail_wit_8_1 := by
  unfold maxSlidingWindow_entail_wit_8_1
  right
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_2 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_2 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_3 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_3 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_4 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_4 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | assumption
    | omega
    | trivial

theorem proof_of_maxSlidingWindow_entail_wit_8_2 : maxSlidingWindow_entail_wit_8_2 := by
  unfold maxSlidingWindow_entail_wit_8_2
  right
  intro l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | exact (proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_1 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_2 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | exact (proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_2 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_3 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | exact (proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_3 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_4 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | exact (proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_4 l n_pre k_pre out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | assumption
    | omega
    | trivial

theorem proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9 := by
  unfold maxSlidingWindow_entail_wit_9
  right
  intro l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | exact (proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | exact (proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_9_split_goal_3 l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | exact (proof_of_maxSlidingWindow_entail_wit_9_split_goal_3 l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | assumption
    | omega
    | trivial

theorem proof_of_maxSlidingWindow_entail_wit_10_1 : maxSlidingWindow_entail_wit_10_1 := by
  unfold maxSlidingWindow_entail_wit_10_1
  right
  intro l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_10_1_split_goal_1 l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | exact (proof_of_maxSlidingWindow_entail_wit_10_1_split_goal_1 l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | (solve | Goal_apply (proof_of_maxSlidingWindow_entail_wit_10_1_split_goal_2 l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | exact (proof_of_maxSlidingWindow_entail_wit_10_1_split_goal_2 l n_pre k_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | assumption
    | omega
    | trivial

theorem proved_auto_solver_maxSlidingWindow_entail_wit_10_2 : maxSlidingWindow_entail_wit_10_2 := by
  unfold maxSlidingWindow_entail_wit_10_2
  intro l nums_pre n_pre k_pre out_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  Exists out_l_2 q_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | trivial

theorem proved_auto_solver_maxSlidingWindow_entail_wit_11 : maxSlidingWindow_entail_wit_11 := by
  unfold maxSlidingWindow_entail_wit_11
  intro l nums_pre n_pre k_pre out_pre out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  Exists out_l_2 q_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | trivial

theorem proof_of_maxSlidingWindow_entail_wit_12 : maxSlidingWindow_entail_wit_12 := by
  unfold maxSlidingWindow_entail_wit_12
  right
  intro l n k out_l out_idx tail head i q hi hk hkn hn hl hq hi0 hin hh hht hti ho hon hok hko hnon hb hu hlen hp hs hqb hqu
  have he : out_idx = n-k+1 := by
    have hv := hko (show k ≤ i by omega)
    omega
  have hresult : SlidingWindowMaximum l k out_l := by
    refine ⟨by omega, ?_⟩
    intro idx hidx
    exact hp idx (by omega)
  sep_apply (naive_C_Rules.IntArray.full_to_undef_full (&("q")) n q)
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg (&("q")) n)
  sep_apply (naive_C_Rules.IntArray.undef_seg_merge_to_undef_full (&("q")) 0 n 100000 ⟨by omega, hn⟩)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero, he]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proved_auto_solver_maxSlidingWindow_return_wit_1 : maxSlidingWindow_return_wit_1 := by
  unfold maxSlidingWindow_return_wit_1
  intro l nums n k out out_l head tail out_idx hh ht ho hp
  Exists out_l
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact hp

end SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_proof_manual
