import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_goal
import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open choosing_inns_goal choosing_inns_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

-- Previously proved auxiliary statements retained for proof audits.
private theorem forall_indexed (P : Int → Prop) (l : List Int) :
    Forall P l ↔ ∀ i, 0 ≤ i ∧ i < Zlength l → P (Znth i l 0) := by
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

private theorem sublist_zlen (lo hi : Int) (l : List Int)
    (hb : 0 ≤ lo ∧ lo ≤ hi) (he : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi - lo := by
  unfold Zlength
  rw [sublist_length lo hi l hb he]
  simp only [Int.ofNat_eq_coe]
  exact Int.toNat_of_nonneg (by omega)

private theorem range_eq_annotation (xs ys : List Int) (lo hi : Int)
    (hb : 0 ≤ lo ∧ lo ≤ hi) (hx : hi ≤ Zlength xs) (hy : hi ≤ Zlength ys)
    (h : ∀ j, lo ≤ j ∧ j < hi → Znth j xs 0 = Znth j ys 0) :
    Forall2 Eq (sublist lo hi xs) (sublist lo hi ys) := by
  have hlx := sublist_zlen lo hi xs hb hx
  have hly := sublist_zlen lo hi ys hb hy
  rw [Forall2_nth_iff Int Int _ _ _ 0 0]
  constructor
  · change ((sublist lo hi xs).length : Int) = hi-lo at hlx
    change ((sublist lo hi ys).length : Int) = hi-lo at hly
    omega
  · intro n hn
    have hn' : (n : Int) < hi-lo := by
      change ((sublist lo hi xs).length : Int) = hi-lo at hlx
      omega
    change Znth (n : Int) (sublist lo hi xs) 0 = Znth (n : Int) (sublist lo hi ys) 0
    rw [Znth_sublist 0 lo n hi xs hb.1 (by omega), Znth_sublist 0 lo n hi ys hb.1 (by omega)]
    exact h (n+lo) (by omega)

private theorem copied_prefix_to_annotation (src old dst : List Int) (written k : Int)
    (hs : Zlength src = k) (ho : Zlength old = k) (hd : Zlength dst = k)
    (hw : 0 ≤ written ∧ written ≤ k) (h : CopyCountsPrefix src old dst written k) :
    InnsCopiedPrefix src old dst written k := by
  constructor
  · exact range_eq_annotation dst src 0 written (by omega) (by omega) (by omega) h.1
  · exact range_eq_annotation dst old written k (by omega) (by omega) (by omega) h.2

private theorem count_safe_annotation (xs : List Int) (k limit : Int) (h : CountArraySafe xs k limit) :
    Zlength xs = k ∧ Forall (LE.le (0 : Int)) xs ∧ Forall (GE.ge limit) xs := by
  have hl := h.1
  refine ⟨h.1, ?_, ?_⟩
  · rw [forall_indexed]; intro i hi; exact (h.2 i (by omega)).1
  · rw [forall_indexed]; intro i hi; exact (h.2 i (by omega)).2

private theorem count_from_annotation (xs : List Int) (k limit : Int)
    (hl : Zlength xs = k) (hlo : Forall (LE.le (0 : Int)) xs) (hhi : Forall (GE.ge limit) xs) :
    CountArraySafe xs k limit := by
  refine ⟨hl, ?_⟩
  intro i hi
  exact ⟨(forall_indexed _ _).mp hlo i (by omega), (forall_indexed _ _).mp hhi i (by omega)⟩

private theorem zero_from_annotation (xs : List Int) (k : Int)
    (hl : Zlength xs = k) (hz : Forall (Eq (0 : Int)) xs) : CountsZeroFull k xs := by
  refine ⟨hl, ?_⟩
  intro i hi
  exact ((forall_indexed _ _).mp hz i (by omega)).symm

private theorem input_from_annotation (colors costs : List Int) (n k p : Int)
    (hn0 : 0 ≤ n) (hn1 : n ≤ 200000) (hk0 : 1 ≤ k) (hk1 : k ≤ 50)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 100) (hc : Zlength colors = n) (ht : Zlength costs = n)
    (hc0 : Forall (LE.le (0 : Int)) colors) (hc1 : Forall (GE.ge (k-1)) colors)
    (ht0 : Forall (LE.le (0 : Int)) costs) (ht1 : Forall (GE.ge (100 : Int)) costs) :
    ChoosingInputSafe colors costs n k p := by
  refine ⟨⟨hn0, hn1⟩, ⟨hk0, hk1⟩, ⟨hp0, hp1⟩, hc, ht, ?_, ?_⟩
  · intro i hi
    have h0 := (forall_indexed _ _).mp hc0 i (by omega)
    have h1 := (forall_indexed _ _).mp hc1 i (by omega)
    omega
  · intro i hi
    exact ⟨(forall_indexed _ _).mp ht0 i (by omega), (forall_indexed _ _).mp ht1 i (by omega)⟩

macro "inns_math" : tactic => `(tactic|
  first
  | assumption
  | omega
  | (apply input_from_annotation <;> assumption)
  | (apply count_from_annotation <;> assumption)
  | (apply zero_from_annotation <;> assumption)
  | (unfold ChoosingPrefixDataSafe; refine ⟨⟨by omega, by omega⟩, by omega, ?_, ?_⟩ <;>
      (apply count_from_annotation <;> first | assumption | omega)))

private theorem forall_zero_snoc (xs : List Int) (h : Forall (Eq (0 : Int)) xs) :
    Forall (Eq (0 : Int)) (xs ++ [0]) := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h.mem hx
  · exact (List.mem_singleton.mp hx).symm


private theorem annotation_Forall_nth (P : Int → Prop) (l : List Int) (i d : Int)
    (h : Forall P l) (hd : P d) : P (Znth i l d) := by
  by_cases hi : i.toNat < l.length
  · have hp := h.mem (List.getElem_mem (l := l) hi)
    simpa only [Znth, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some] using hp
  · simpa only [Znth, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega : l.length ≤ i.toNat), Option.getD_none] using hd

private theorem forall2_eq {xs ys : List Int} (h : Forall2 Eq xs ys) : xs = ys := by
  induction h with
  | nil => rfl
  | cons he _ ih => exact congrArg₂ List.cons he ih

private theorem copied_prefix_from_annotation (src old dst : List Int) (written k : Int)
    (hw : 0 ≤ written) (h : InnsCopiedPrefix src old dst written k) :
    CopyCountsPrefix src old dst written k := by
  have hf := forall2_eq h.1
  have hs := forall2_eq h.2
  constructor
  · intro idx hi
    have he := congrArg (fun xs => Znth idx xs (0 : Int)) hf
    simpa only [Znth_sublist 0 0 idx written dst (by omega) (by omega),
      Znth_sublist 0 0 idx written src (by omega) (by omega), Int.add_zero] using he
  · intro idx hi
    have he := congrArg (fun xs => Znth (idx-written) xs (0 : Int)) hs
    dsimp only at he
    rw [Znth_sublist 0 written (idx-written) k dst hw (by omega),
      Znth_sublist 0 written (idx-written) k old hw (by omega)] at he
    simpa only [Int.sub_add_cancel] using he


theorem proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1 := by
  unfold initCounts_entail_wit_1
  right
  intro k hk hl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact Forall.nil | simp [Zlength]

theorem proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2 := by
  unfold initCounts_entail_wit_2
  right
  intro k good seen i hi hk0 hk hi0 hik hslen hs hglen hg
  have hseen := forall_zero_snoc seen hs
  have hgood := forall_zero_snoc good hg
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_initCounts_return_wit_1 : initCounts_return_wit_1 := by
  unfold initCounts_return_wit_1
  right
  intro k good_ptr seen_ptr good seen i hik hk0 hk hi0 hik' hslen hs hglen hg
  have hi : i = k := by omega
  subst i
  Exists good
  Exists seen
  split_pure_spatial
  · rw [hi]
    sep_apply (intArray.seg_to_full seen_ptr 0 k seen)
    sep_apply (intArray.seg_to_full good_ptr 0 k good)
    simp only [Int.sub_zero, Int.zero_mul, Int.add_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem aux_copyCounts_entail_wit_1_split_goal_1 : (forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000)) (PreH4 : (CountArraySafe good_old k_pre 200000)) ,
  (CopyCountsPrefix seen_l good_old good_old (0 : Int) k_pre)) := by

  intro k_pre good_old seen_l PreH1 PreH2 PreH3 PreH4
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    exact CopyCountsPrefix_zero seen_l good_old k_pre PreH3.1 PreH4.1

theorem proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1 := by
  unfold copyCounts_entail_wit_1
  right
  intro k_pre good_old seen_l NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  have PreH1 : (1 <= k_pre) := NewPreH1
  have PreH2 : (k_pre <= 50) := NewPreH2
  have PreH3 : (CountArraySafe seen_l k_pre 200000) := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    have hb0 := annotation_Forall_nth _ seen_l idx 0 NewPreH4 (by omega)
    have hb1 := annotation_Forall_nth _ seen_l idx 0 NewPreH5 (by omega)
    omega
  have PreH4 : (CountArraySafe good_old k_pre 200000) := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    have hb0 := annotation_Forall_nth _ good_old idx 0 NewPreH7 (by omega)
    have hb1 := annotation_Forall_nth _ good_old idx 0 NewPreH8 (by omega)
    omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact copied_prefix_to_annotation seen_l good_old good_old 0 k_pre PreH3.1 PreH4.1 PreH4.1 (by omega) (aux_copyCounts_entail_wit_1_split_goal_1 k_pre good_old seen_l PreH1 PreH2 PreH3 PreH4)


theorem aux_copyCounts_entail_wit_2_split_goal_1 : (forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre)) ,
  (CopyCountsPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)) (i + 1) k_pre)) := by

  intro k_pre good_old seen_l good_cur_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    exact CopyCountsPrefix_step_replace seen_l good_old good_cur_2 i k_pre PreH9 PreH8.1 ⟨PreH4, PreH1⟩

theorem aux_copyCounts_entail_wit_2_split_goal_2 : (forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre)) ,
  (CountArraySafe (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)) k_pre 200000)) := by

  intro k_pre good_old seen_l good_cur_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    refine ⟨?_, ?_⟩
    · simpa only [Zlength_replace_Znth] using PreH8.1
    · exact replace_Znth_preserves_bounds good_cur_2 i (Znth i seen_l 0) k_pre 0 200000 PreH8.1 ⟨PreH4, PreH1⟩
        (PreH6.2 i ⟨PreH4, PreH1⟩) PreH8.2

theorem proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2 := by
  unfold copyCounts_entail_wit_2
  right
  intro k_pre good_old seen_l good_cur_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  have PreH1 : (i < k_pre) := NewPreH1
  have PreH2 : (1 <= k_pre) := NewPreH2
  have PreH3 : (k_pre <= 50) := NewPreH3
  have PreH4 : ((0 : Int) <= i) := NewPreH4
  have PreH5 : (i <= k_pre) := NewPreH5
  have PreH6 : (CountArraySafe seen_l k_pre 200000) := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    have hb0 := annotation_Forall_nth _ seen_l idx 0 NewPreH7 (by omega)
    have hb1 := annotation_Forall_nth _ seen_l idx 0 NewPreH8 (by omega)
    omega
  have PreH7 : (CountArraySafe good_old k_pre 200000) := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    have hb0 := annotation_Forall_nth _ good_old idx 0 NewPreH10 (by omega)
    have hb1 := annotation_Forall_nth _ good_old idx 0 NewPreH11 (by omega)
    omega
  have PreH8 : (CountArraySafe good_cur_2 k_pre 200000) := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    have hb0 := annotation_Forall_nth _ good_cur_2 idx 0 NewPreH13 (by omega)
    have hb1 := annotation_Forall_nth _ good_cur_2 idx 0 NewPreH14 (by omega)
    omega
  have PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre) := copied_prefix_from_annotation _ _ _ _ _ (by omega) NewPreH15
  have hb := count_safe_annotation _ _ _ (aux_copyCounts_entail_wit_2_split_goal_2 k_pre good_old seen_l good_cur_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
  have hp := copied_prefix_to_annotation seen_l good_old _ (i+1) k_pre PreH6.1 PreH7.1 hb.1 (by omega) (aux_copyCounts_entail_wit_2_split_goal_1 k_pre good_old seen_l good_cur_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))




      | exact hp
      | exact hb.1
      | exact hb.2.1
      | exact hb.2.2

theorem proof_of_copyCounts_return_wit_1_split_goal_1 : copyCounts_return_wit_1_split_goal_1 := by
  unfold copyCounts_return_wit_1_split_goal_1
  intro k_pre good_old seen_l good_cur i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i >= k_pre) := NewPreH1
    have PreH5 : (i <= k_pre) := NewPreH5
    have PreH6 : (CountArraySafe seen_l k_pre 200000) := by
      refine ⟨by omega, ?_⟩
      intro idx hi
      have hb0 := annotation_Forall_nth _ seen_l idx 0 NewPreH7 (by omega)
      have hb1 := annotation_Forall_nth _ seen_l idx 0 NewPreH8 (by omega)
      omega
    have PreH8 : (CountArraySafe good_cur k_pre 200000) := by
      refine ⟨by omega, ?_⟩
      intro idx hi
      have hb0 := annotation_Forall_nth _ good_cur idx 0 NewPreH13 (by omega)
      have hb1 := annotation_Forall_nth _ good_cur idx 0 NewPreH14 (by omega)
      omega
    have PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre) := copied_prefix_from_annotation _ _ _ _ _ (by omega) NewPreH15
    exact CopyCountsPrefix_full_eq seen_l good_old good_cur i k_pre PreH9 PreH6.1 PreH8.1 PreH1 PreH5

theorem proof_of_copyCounts_return_wit_1 : copyCounts_return_wit_1 := by
  unfold copyCounts_return_wit_1
  right
  intro k_pre good_old seen_l good_cur i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  have PreH1 : (i >= k_pre) := NewPreH1
  have PreH2 : (1 <= k_pre) := NewPreH2
  have PreH3 : (k_pre <= 50) := NewPreH3
  have PreH4 : ((0 : Int) <= i) := NewPreH4
  have PreH5 : (i <= k_pre) := NewPreH5
  have PreH6 : (CountArraySafe seen_l k_pre 200000) := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    have hb0 := annotation_Forall_nth _ seen_l idx 0 NewPreH7 (by omega)
    have hb1 := annotation_Forall_nth _ seen_l idx 0 NewPreH8 (by omega)
    omega
  have PreH7 : (CountArraySafe good_old k_pre 200000) := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    have hb0 := annotation_Forall_nth _ good_old idx 0 NewPreH10 (by omega)
    have hb1 := annotation_Forall_nth _ good_old idx 0 NewPreH11 (by omega)
    omega
  have PreH8 : (CountArraySafe good_cur k_pre 200000) := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    have hb0 := annotation_Forall_nth _ good_cur idx 0 NewPreH13 (by omega)
    have hb1 := annotation_Forall_nth _ good_cur idx 0 NewPreH14 (by omega)
    omega
  have PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre) := copied_prefix_from_annotation _ _ _ _ _ (by omega) NewPreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_copyCounts_return_wit_1_split_goal_1 k_pre good_old seen_l good_cur i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15


theorem proof_of_countChoosingInns_entail_wit_1 : countChoosingInns_entail_wit_1 := by
  unfold countChoosingInns_entail_wit_1
  right
  intro p_pre k_pre n_pre costs_l colors_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  sep_apply (naive_C_Rules.IntArray.undef_full_split_to_undef_seg (&("seen")) k_pre 50 (by omega))
  sep_apply (naive_C_Rules.IntArray.undef_full_split_to_undef_seg (&("good")) k_pre 50 (by omega))
  sep_apply (naive_C_Rules.IntArray.undef_seg_to_undef_full (&("seen")) 0 k_pre)
  sep_apply (naive_C_Rules.IntArray.undef_seg_to_undef_full (&("good")) 0 k_pre)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel


theorem proof_of_countChoosingInns_entail_wit_2 : countChoosingInns_entail_wit_2 := by
  unfold countChoosingInns_entail_wit_2
  right
  intro p_pre k_pre n_pre costs_l colors_l answer good_l_2 seen_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hs := zero_from_annotation seen_l_2 k_pre PreH1 PreH2
  have hg := zero_from_annotation good_l_2 k_pre PreH3 PreH4
  have hp := CountsZeroFull_to_ChoosingPrefixState_zero colors_l costs_l k_pre p_pre seen_l_2 good_l_2 hs hg
  have hs0 : CountArraySafe seen_l_2 k_pre 0 := ⟨hs.1, by intro i hi; have := hs.2 i hi; omega⟩
  have hg0 : CountArraySafe good_l_2 k_pre 0 := ⟨hg.1, by intro i hi; have := hg.2 i hi; omega⟩
  have hb1 := count_safe_annotation _ _ _ hs0
  have hb2 := count_safe_annotation _ _ _ hg0
  subst answer
  Exists good_l_2 seen_l_2
  simp only [Int.zero_mul, Int.add_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | exact hb1.2.1 | exact hb1.2.2 | exact hb2.2.1 | exact hb2.2.2


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_1 : countChoosingInns_entail_wit_3_split_goal_1 := by
  unfold countChoosingInns_entail_wit_3_split_goal_1
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2) := by inns_math
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    have hb := PreH7.2.2.1.2 (Znth i colors_l 0) hc
    have hn := PreH2.1
    simp only [INT_MAX]
    omega

theorem proof_of_countChoosingInns_entail_wit_3_split_goal_2 : countChoosingInns_entail_wit_3_split_goal_2 := by
  unfold countChoosingInns_entail_wit_3_split_goal_2
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2) := by inns_math
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    have hb := PreH7.2.2.2.2 (Znth i colors_l 0) hc
    have hn := PreH2.1
    omega

theorem proof_of_countChoosingInns_entail_wit_3_split_goal_3 : countChoosingInns_entail_wit_3_split_goal_3 := by
  unfold countChoosingInns_entail_wit_3_split_goal_3
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2) := by inns_math
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    have hb := PreH7.2.2.1.2 (Znth i colors_l 0) hc
    have hn := PreH2.1
    omega

theorem proof_of_countChoosingInns_entail_wit_3_split_goal_4 : countChoosingInns_entail_wit_3_split_goal_4 := by
  unfold countChoosingInns_entail_wit_3_split_goal_4
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2) := by inns_math
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    have hb := PreH7.2.2.2.2 (Znth i colors_l 0) hc
    omega

theorem proof_of_countChoosingInns_entail_wit_3_split_goal_5 : countChoosingInns_entail_wit_3_split_goal_5 := by
  unfold countChoosingInns_entail_wit_3_split_goal_5
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2) := by inns_math
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    have hb := PreH7.2.2.2.2 (Znth i colors_l 0) hc
    omega

theorem proof_of_countChoosingInns_entail_wit_3_split_goal_6 : countChoosingInns_entail_wit_3_split_goal_6 := by
  unfold countChoosingInns_entail_wit_3_split_goal_6
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2) := by inns_math
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    have hb := PreH7.2.2.1.2 (Znth i colors_l 0) hc
    omega

theorem proof_of_countChoosingInns_entail_wit_3_split_goal_7 : countChoosingInns_entail_wit_3_split_goal_7 := by
  unfold countChoosingInns_entail_wit_3_split_goal_7
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2) := by inns_math
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    have hb := PreH7.2.2.1.2 (Znth i colors_l 0) hc
    omega

theorem proof_of_countChoosingInns_entail_wit_3_split_goal_8 : countChoosingInns_entail_wit_3_split_goal_8 := by
  unfold countChoosingInns_entail_wit_3_split_goal_8
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    have hb := PreH2.2.2.2.2.2.2 i ⟨PreH3, PreH1⟩
    omega

theorem proof_of_countChoosingInns_entail_wit_3_split_goal_9 : countChoosingInns_entail_wit_3_split_goal_9 := by
  unfold countChoosingInns_entail_wit_3_split_goal_9
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    have hb := PreH2.2.2.2.2.2.2 i ⟨PreH3, PreH1⟩
    omega

theorem proof_of_countChoosingInns_entail_wit_3_split_goal_10 : countChoosingInns_entail_wit_3_split_goal_10 := by
  unfold countChoosingInns_entail_wit_3_split_goal_10
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    omega

theorem proof_of_countChoosingInns_entail_wit_3_split_goal_11 : countChoosingInns_entail_wit_3_split_goal_11 := by
  unfold countChoosingInns_entail_wit_3_split_goal_11
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (i < n_pre) := NewPreH1
    have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
    have PreH3 : ((0 : Int) <= i) := NewPreH14
    have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
    omega

theorem proof_of_countChoosingInns_entail_wit_3 : countChoosingInns_entail_wit_3 := by
  unfold countChoosingInns_entail_wit_3
  right
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  have PreH1 : (i < n_pre) := NewPreH1
  have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
  have PreH3 : ((0 : Int) <= i) := NewPreH14
  have PreH4 : (i <= n_pre) := NewPreH15
  have PreH5 : ((0 : Int) <= answer) := NewPreH16
  have PreH6 : (answer <= 19999900000) := NewPreH17
  have PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2) := by inns_math
  have PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2) := by inns_math
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_1 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_2 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_3 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_4 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_5 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_6 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_7 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_8 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_9 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_10 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_11 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27


theorem proof_of_countChoosingInns_entail_wit_4 : countChoosingInns_entail_wit_4 := by
  unfold countChoosingInns_entail_wit_4
  right
  intro p_pre k_pre n_pre costs_l colors_l seen_l good_l_2 c i cost answer NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40
  have PreH2 : (c = (Znth i colors_l (0 : Int))) := NewPreH2
  have PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
  have PreH5 : ((0 : Int) <= i) := NewPreH16
  have PreH7 : ((0 : Int) <= c) := NewPreH18
  have PreH8 : (c < k_pre) := NewPreH19
  have PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l_2) := by inns_math
  have PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l_2) := by inns_math
  have hlen := PreH4.2.2.2.1
  have hn := PreH4.1
  have hid : i < Zlength colors_l := by omega
  have hdata := ChoosingPrefixDataSafe_step_expensive colors_l costs_l i k_pre seen_l good_l_2 c PreH20 hid ⟨PreH7, PreH8⟩
  have hfull := ChoosingPrefixDataSafe_step_affordable_after_copy colors_l costs_l i k_pre seen_l good_l_2 c PreH20 hid ⟨PreH7, PreH8⟩
  have hstate := ChoosingPrefixState_step_affordable_after_copy colors_l costs_l i k_pre p_pre answer (answer + Znth c seen_l 0)
    seen_l good_l_2 (replace_Znth c (Znth c seen_l 0 + 1) seen_l) c PreH20 PreH21 ⟨PreH5, hid⟩ ⟨PreH7, PreH8⟩ PreH2 (by omega) rfl rfl
  have hbound := ChoosingPrefixState_answer_bound colors_l costs_l (i + 1) k_pre p_pre (answer + Znth c seen_l 0)
    (replace_Znth c (Znth c seen_l 0 + 1) seen_l) (replace_Znth c (Znth c seen_l 0 + 1) seen_l) n_pre hfull hstate (by omega) hn.2
  have hs200 := CountArraySafe_weaken_limit _ k_pre (i + 1) 200000 hdata.2.2.1 (by omega)
  have hg200 := CountArraySafe_weaken_limit _ k_pre (i + 1) 200000 hdata.2.2.2 (by omega)
  rcases count_safe_annotation _ _ _ hdata.2.2.1 with ⟨hslen, hslo, hshi⟩
  rcases count_safe_annotation _ _ _ hdata.2.2.2 with ⟨hglen, hglo, hghi⟩
  rcases count_safe_annotation _ _ _ hs200 with ⟨_, _, hsbound⟩
  rcases count_safe_annotation _ _ _ hg200 with ⟨_, _, hgbound⟩
  subst c
  Exists good_l_2 seen_l
  simp only [Int.zero_mul, Int.add_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | rfl | assumption | omega | simpa only [Int.add_sub_cancel] using PreH21

theorem aux_countChoosingInns_entail_wit_5_split_goal_1 : (forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next_2 : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c < k_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next_2 good_l)) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH18 : (CountArraySafe good_l k_pre 200000)) ,
  (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre answer seen_next_2 seen_next_2)) := by

  intro p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have hlen := PreH4.2.2.2.1
    exact ChoosingPrefixState_step_affordable_after_copy colors_l costs_l i k_pre p_pre (answer - Znth c seen_l 0) answer
      seen_l good_l seen_next_2 c PreH14 PreH16 (by omega) ⟨PreH9, PreH10⟩ PreH2 (by omega) (by omega) PreH13

theorem aux_countChoosingInns_entail_wit_5_split_goal_2 : (forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next_2 : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c < k_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next_2 good_l)) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH18 : (CountArraySafe good_l k_pre 200000)) ,
  (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next_2 seen_next_2)) := by

  intro p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    subst seen_next_2
    have hlen := PreH4.2.2.2.1
    exact ChoosingPrefixDataSafe_step_affordable_after_copy colors_l costs_l i k_pre seen_l good_l c PreH14 (by omega) ⟨PreH9, PreH10⟩

theorem proof_of_countChoosingInns_entail_wit_5 : countChoosingInns_entail_wit_5 := by
  unfold countChoosingInns_entail_wit_5
  right
  intro p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47 NewPreH48
  have PreH1 : (CountArraySafe seen_next_2 k_pre 200000) := by inns_math
  have PreH2 : (c = (Znth i colors_l (0 : Int))) := NewPreH1
  have PreH3 : (cost = (Znth i costs_l (0 : Int))) := NewPreH2
  have PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
  have PreH5 : ((0 : Int) <= cost) := NewPreH15
  have PreH6 : (cost <= p_pre) := NewPreH16
  have PreH7 : ((0 : Int) <= i) := NewPreH17
  have PreH8 : (i < n_pre) := NewPreH18
  have PreH9 : ((0 : Int) <= c) := NewPreH19
  have PreH10 : (c < k_pre) := NewPreH20
  have PreH11 : ((0 : Int) <= answer) := NewPreH21
  have PreH12 : (answer <= 19999900000) := NewPreH22
  have PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l))) := NewPreH23
  have PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) := by inns_math
  have PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next_2 good_l) := by inns_math
  have PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l) := by inns_math
  have PreH17 : (CountArraySafe seen_next_2 k_pre 200000) := by inns_math
  have PreH18 : (CountArraySafe good_l k_pre 200000) := by inns_math
  have hp := aux_countChoosingInns_entail_wit_5_split_goal_1 p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hd := aux_countChoosingInns_entail_wit_5_split_goal_2 p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rcases count_safe_annotation _ _ _ hd.2.2.1 with ⟨hslen, hslo, hshi⟩
  Exists seen_next_2
  simp only [Int.zero_mul, Int.add_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_countChoosingInns_entail_wit_6 : countChoosingInns_entail_wit_6 := by
  unfold countChoosingInns_entail_wit_6
  right
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l c i cost answer NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40
  have PreH2 : (c = (Znth i colors_l (0 : Int))) := NewPreH2
  have PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
  have PreH5 : ((0 : Int) <= i) := NewPreH16
  have PreH7 : ((0 : Int) <= c) := NewPreH18
  have PreH8 : (c < k_pre) := NewPreH19
  have PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l) := by inns_math
  have PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l) := by inns_math
  have hlen := PreH4.2.2.2.1
  have hn := PreH4.1
  have hid : i < Zlength colors_l := by omega
  have hdata := ChoosingPrefixDataSafe_step_expensive colors_l costs_l i k_pre seen_l_2 good_l c PreH20 hid ⟨PreH7, PreH8⟩
  have hstate := ChoosingPrefixState_step_expensive colors_l costs_l i k_pre p_pre answer (answer + Znth c good_l 0)
    seen_l_2 good_l (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2) c PreH20 PreH21 ⟨PreH5, hid⟩ ⟨PreH7, PreH8⟩ PreH2 (by omega) rfl rfl
  have hbound := ChoosingPrefixState_answer_bound colors_l costs_l (i + 1) k_pre p_pre (answer + Znth c good_l 0)
    (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2) good_l n_pre hdata hstate (by omega) hn.2
  have hlseen := PreH20.2.2.1.1
  rcases count_safe_annotation _ _ _ hdata.2.2.1 with ⟨hslen, hslo, hshi⟩
  rcases count_safe_annotation _ _ _ hdata.2.2.2 with ⟨hglen, hglo, hghi⟩
  subst c
  rw [hlseen]
  Exists seen_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | rfl | assumption | omega | simpa only [Int.add_sub_cancel] using PreH21

theorem proof_of_countChoosingInns_entail_wit_8 : countChoosingInns_entail_wit_8 := by
  unfold countChoosingInns_entail_wit_8
  right
  intro p_pre k_pre n_pre costs_l colors_l good_l seen_l answer i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27
  have PreH1 : (i >= n_pre) := NewPreH1
  have PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) := by inns_math
  have PreH3 : ((0 : Int) <= i) := NewPreH14
  have PreH4 : (i <= n_pre) := NewPreH15
  have PreH5 : ((0 : Int) <= answer) := NewPreH16
  have PreH6 : (answer <= 19999900000) := NewPreH17
  have PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) := by inns_math
  have PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l) := by inns_math
  have he : i = n_pre := by omega
  have hp : InnsPairAnswer colors_l costs_l n_pre p_pre answer := by simpa only [he] using PreH8.1
  sep_apply (naive_C_Rules.IntArray.full_to_undef_full (&("seen")) k_pre seen_l)
  sep_apply (naive_C_Rules.IntArray.full_to_undef_full (&("good")) k_pre good_l)
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg (&("seen")) k_pre)
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg (&("good")) k_pre)
  sep_apply (naive_C_Rules.IntArray.undef_seg_merge_to_undef_full (&("seen")) 0 k_pre 50 (by omega))
  sep_apply (naive_C_Rules.IntArray.undef_seg_merge_to_undef_full (&("good")) 0 k_pre 50 (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  split_pure_spatial
  · exact naive_C_Rules.toContext.derivable1_sepcon_comm _ _
  · dump_pre_spatial
    exact hp


end SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_proof_manual
