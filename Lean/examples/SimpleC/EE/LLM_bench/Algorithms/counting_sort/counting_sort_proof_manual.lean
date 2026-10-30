import SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_goal
import SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open counting_sort_goal counting_sort_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem nth_mem (l : List Int) (i : Int) (h : 0 ≤ i ∧ i < Zlength l) :
    Znth i l 0 ∈ l := by
  unfold Znth
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [Zlength, Int.ofNat_eq_coe] at h; omega)]
  simp only [Option.getD_some]
  exact List.getElem_mem _

-- Previously proved auxiliary statements retained for proof audits.
private theorem annotation_Forall_nth {A : Type} (P : A → Prop) (l : List A) (i : Int) (d : A)
    (h : Forall P l) (hd : P d) : P (Znth i l d) := by
  by_cases hi : i.toNat < l.length
  · have hp := h.mem (List.getElem_mem (l := l) hi)
    simpa only [Znth, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some] using hp
  · simpa only [Znth, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega : l.length ≤ i.toNat), Option.getD_none] using hd

private theorem annotation_Forall_nth_in {A : Type} (P : A → Prop) (l : List A) (i : Int) (d : A)
    (h : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  have hin : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  have hp := h.mem (List.getElem_mem (l := l) hin)
  simpa only [Znth, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hin, Option.getD_some] using hp



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

private theorem forall_weaken {A : Type} {P Q : A → Prop} {l : List A}
    (hp : Forall P l) (hi : ∀ x, P x → Q x) : Forall Q l :=
  Forall.iff_forall_mem.mpr (by intro x hx; exact hi x (hp.mem hx))

private theorem forall_replace {A : Type} (P : A → Prop) (d x : A) (l : List A)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) (hp : Forall P l) (hx : P x) :
    Forall P (replace_Znth i x l) := by
  apply (indexed_Forall P _ d).mpr
  intro j hj
  rw [Zlength_replace_Znth] at hj
  by_cases he : i = j
  · subst j; rw [Znth_replace_Znth_Same d l i x hi]; exact hx
  · rw [Znth_replace_Znth_Diff d l i j x hi hj he]
    exact (indexed_Forall P l d).mp hp j hj

private theorem bounds_index (l : List Int) (lo hi i : Int)
    (hl : Forall (LE.le lo) l) (hh : Forall (GE.ge hi) l)
    (hr : 0 ≤ i ∧ i < Zlength l) : lo ≤ Znth i l 0 ∧ Znth i l 0 ≤ hi :=
  ⟨annotation_Forall_nth_in _ l i 0 hl hr, annotation_Forall_nth_in _ l i 0 hh hr⟩

private theorem indexed_bounds (l : List Int) (lo hi : Int)
    (hb : ∀ i, 0 ≤ i ∧ i < Zlength l → lo ≤ Znth i l 0 ∧ Znth i l 0 ≤ hi) :
    Forall (LE.le lo) l ∧ Forall (GE.ge hi) l :=
  ⟨(indexed_Forall _ l 0).mpr (by intro i hi; exact (hb i hi).1),
   (indexed_Forall _ l 0).mpr (by intro i hi; exact (hb i hi).2)⟩

private theorem value_bounds (l : List Int) (i : Int)
    (hl : Forall (LE.le (0 : Int)) l) (hh : Forall (GT.gt (100 : Int)) l)
    (hr : 0 ≤ i ∧ i < Zlength l) : 0 ≤ Znth i l 0 ∧ Znth i l 0 < 100 :=
  ⟨annotation_Forall_nth_in _ l i 0 hl hr, annotation_Forall_nth_in _ l i 0 hh hr⟩

theorem proof_of_sort_entail_wit_2_split_goal_1 : sort_entail_wit_2_split_goal_1 := by
  unfold sort_entail_wit_2_split_goal_1
  intro input n_pre value count_mixed_2 output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (value < 100) := NewPreH1
    have PreH6 : ((Zlength (count_mixed_2)) = 100) := NewPreH6
    have PreH7 : ((0 : Int) <= value) := NewPreH7
    have PreH11 : (CountingZeroedPrefix count_mixed_2 value) := NewPreH12
    exact counting_zeroed_prefix_replace__initial_zeroing count_mixed_2 value PreH6 ⟨PreH7, PreH1⟩ PreH11

theorem proof_of_sort_entail_wit_2_split_goal_2 : sort_entail_wit_2_split_goal_2 := by
  unfold sort_entail_wit_2_split_goal_2
  intro input n_pre value count_mixed_2 output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH6 : ((Zlength (count_mixed_2)) = 100) := NewPreH6
    simpa only [Zlength_replace_Znth] using PreH6

theorem proof_of_sort_entail_wit_5_split_goal_1 : sort_entail_wit_5_split_goal_1 := by
  unfold sort_entail_wit_5_split_goal_1
  intro input n_pre i output_mixed_2 counts_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : ((0 : Int) <= (Znth i input (0 : Int))) := NewPreH1
    have PreH2 : ((Znth i input (0 : Int)) < 100) := NewPreH2
    have PreH18 : (CountingHistogramPrefix input counts_2 i) := NewPreH20
    intro bucket hb
    have hf := counting_frequency_prefix_snoc__histogram_cumulative input i bucket (by omega)
    by_cases he : Znth i input 0 = bucket
    · subst bucket
      rw [Znth_replace_Znth_Same 0 counts_2 _ _ (by omega), hf, PreH18 _ ⟨PreH1, PreH2⟩]
      simp
    · rw [Znth_replace_Znth_Diff 0 counts_2 _ bucket _ (by omega) (by omega) he, hf, PreH18 bucket hb]
      simp [he]

theorem proof_of_sort_entail_wit_5_split_goal_4 : sort_entail_wit_5_split_goal_4 := by
  unfold sort_entail_wit_5_split_goal_4
  intro input n_pre i output_mixed_2 counts_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH12 : ((Zlength (counts_2)) = 100) := NewPreH12
    simpa only [Zlength_replace_Znth] using PreH12

theorem proof_of_sort_entail_wit_6_split_goal_1 : sort_entail_wit_6_split_goal_1 := by
  unfold sort_entail_wit_6_split_goal_1
  intro input n_pre i counts output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : ((Zlength (input)) = n_pre) := NewPreH4
    have PreH12 : (CountingHistogramPrefix input counts i) := NewPreH14
    have he : i = n_pre := by omega
    subst i
    intro bucket hb
    have hh := PreH12 bucket hb
    rw [sublist_self input n_pre PreH4.symm] at hh
    rw [hh]
    by_cases hb1 : bucket < 1
    · have he0 : bucket = 0 := by omega
      subst bucket
      simp only [show (0 : Int) < 1 by decide, if_pos]
      unfold CountingCumulativeEnd
      simp
    · rw [if_neg hb1]

theorem proof_of_sort_entail_wit_6_split_goal_2 : sort_entail_wit_6_split_goal_2 := by
  unfold sort_entail_wit_6_split_goal_2
  intro input n_pre i counts output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : ((Zlength (input)) = n_pre) := NewPreH4
    have PreH12 : (CountingHistogramPrefix input counts i) := NewPreH14
    intro _
    have he : i = n_pre := by omega
    subst i
    have hz := PreH12 0 (by omega)
    have ho := PreH12 1 (by omega)
    rw [sublist_self input n_pre PreH4.symm] at hz ho
    have hb := counting_cumulative_end_bound__histogram_cumulative input 1
    have hs := counting_cumulative_end_step__histogram_cumulative input 1 (by omega)
    have hzero : CountingCumulativeEnd input 0 = CountingFrequency input 0 := by simp [CountingCumulativeEnd]
    simp only [show (1 : Int) - 1 = 0 from rfl] at *
    omega

theorem proof_of_sort_entail_wit_7_split_goal_1 : sort_entail_wit_7_split_goal_1 := by
  unfold sort_entail_wit_7_split_goal_1
  intro input n_pre value positions_2 output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH13 : (CountingCumulativeState input positions_2 value) := NewPreH15
    intro bucket hb
    have hold := PreH13 bucket hb
    by_cases hlo : bucket < value
    · rw [Znth_replace_Znth_Diff 0 positions_2 value bucket _ (by omega) (by omega) (by omega), if_pos (by omega)]
      simpa only [if_pos hlo] using hold
    · by_cases he : bucket = value
      · subst bucket
        have hprev := PreH13 (value - 1) (by omega)
        rw [Znth_replace_Znth_Same 0 positions_2 value _ (by omega), if_pos (by omega)]
        rw [if_neg (by omega)] at hold
        rw [if_pos (by omega)] at hprev
        rw [hold, hprev, counting_cumulative_end_step__histogram_cumulative input value (by omega)]
        omega
      · rw [Znth_replace_Znth_Diff 0 positions_2 value bucket _ (by omega) (by omega) (Ne.symm he), if_neg (by omega)]
        simpa only [if_neg hlo] using hold

theorem proof_of_sort_entail_wit_7_split_goal_2 : sort_entail_wit_7_split_goal_2 := by
  unfold sort_entail_wit_7_split_goal_2
  intro input n_pre value positions_2 output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH13 : (CountingCumulativeState input positions_2 value) := NewPreH15
    intro hnext
    rw [Znth_replace_Znth_Diff 0 positions_2 value (value + 1) _ (by omega) (by omega) (by omega)]
    rw [show value + 1 - 1 = value by omega, Znth_replace_Znth_Same 0 positions_2 value _ (by omega)]
    have hn := PreH13 (value + 1) (by omega)
    have hc := PreH13 value (by omega)
    have hp := PreH13 (value - 1) (by omega)
    rw [if_neg (by omega)] at hn hc
    rw [if_pos (by omega)] at hp
    rw [hn, hc, hp]
    have hb := counting_cumulative_end_bound__histogram_cumulative input (value + 1)
    rw [counting_cumulative_end_step__histogram_cumulative input (value + 1) (by omega),
      show value + 1 - 1 = value by omega, counting_cumulative_end_step__histogram_cumulative input value (by omega)] at hb
    omega

theorem proof_of_sort_entail_wit_7_split_goal_5 : sort_entail_wit_7_split_goal_5 := by
  unfold sort_entail_wit_7_split_goal_5
  intro input n_pre value positions_2 output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH6 : ((Zlength (positions_2)) = 100) := NewPreH6
    simpa only [Zlength_replace_Znth] using PreH6

theorem proof_of_sort_entail_wit_9_split_goal_1 : sort_entail_wit_9_split_goal_1 := by
  unfold sort_entail_wit_9_split_goal_1
  intro input n_pre i output_mixed bucket_ends sorted positions NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (i >= (0 : Int)) := NewPreH7
    have PreH16 : (i < n_pre) := NewPreH16
    have PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 100))) := by
      intro k hindex
      have value_PreH17 := annotation_Forall_nth _ input k 0 NewPreH17 (by omega)
      have value_PreH18 := annotation_Forall_nth _ input k 0 NewPreH18 (by omega)
      omega
    have PreH19 : forall (bucket : Int) , ((((0 : Int) <= bucket) ∧ (bucket < 100)) -> (((0 : Int) <= (Znth bucket positions (0 : Int))) ∧ ((Znth bucket positions (0 : Int)) <= n_pre))) := by
      intro bucket hindex
      have value_PreH21 := annotation_Forall_nth _ positions bucket 0 NewPreH21 (by omega)
      have value_PreH22 := annotation_Forall_nth _ positions bucket 0 NewPreH22 (by omega)
      omega
    exact (PreH19 _ (PreH17 i ⟨PreH7, PreH16⟩)).2

theorem proof_of_sort_entail_wit_4_split_goal_3 : sort_entail_wit_4_split_goal_3 := by
  unfold sort_entail_wit_4_split_goal_3
  intro input n_pre i output_mixed counts NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (i >= (0 : Int)) := by first | assumption | omega
    have PreH16 : (i < n_pre) := NewPreH5
    have PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 100))) := by
      intro k hindex
      have value_PreH13 := annotation_Forall_nth _ input k 0 NewPreH13 (by omega)
      have value_PreH14 := annotation_Forall_nth _ input k 0 NewPreH14 (by omega)
      omega
    exact (PreH17 i ⟨PreH7, PreH16⟩).2

theorem proof_of_sort_entail_wit_4_split_goal_4 : sort_entail_wit_4_split_goal_4 := by
  unfold sort_entail_wit_4_split_goal_4
  intro input n_pre i output_mixed counts NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (i >= (0 : Int)) := by first | assumption | omega
    have PreH16 : (i < n_pre) := NewPreH5
    have PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 100))) := by
      intro k hindex
      have value_PreH13 := annotation_Forall_nth _ input k 0 NewPreH13 (by omega)
      have value_PreH14 := annotation_Forall_nth _ input k 0 NewPreH14 (by omega)
      omega
    exact (PreH17 i ⟨PreH7, PreH16⟩).1

theorem proof_of_sort_entail_wit_10_split_goal_1 : sort_entail_wit_10_split_goal_1 := by
  unfold sort_entail_wit_10_split_goal_1
  intro input n_pre i output_mixed bucket_ends sorted positions NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    rw [Znth_replace_Znth_Same 0 positions _ _ (by omega)]
    omega

theorem proof_of_sort_entail_wit_10_split_goal_2 : sort_entail_wit_10_split_goal_2 := by
  unfold sort_entail_wit_10_split_goal_2
  intro input n_pre i output_mixed bucket_ends sorted positions NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    rw [Znth_replace_Znth_Same 0 positions _ _ (by omega)]
    omega

theorem proof_of_sort_entail_wit_13_split_goal_1 : sort_entail_wit_13_split_goal_1 := by
  unfold sort_entail_wit_13_split_goal_1
  intro input n_pre i bucket_starts_2 live_2 sorted_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH12 : (CountingCopyProgress input sorted_2 live_2 i) := NewPreH13
    simp only [Int.sub_zero]
    exact counting_copy_step__copyback input sorted_2 live_2 i (by omega) (by omega) PreH12

theorem proof_of_sort_entail_wit_13_split_goal_2 : sort_entail_wit_13_split_goal_2 := by
  unfold sort_entail_wit_13_split_goal_2
  intro input n_pre i bucket_starts_2 live_2 sorted_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH6 : ((Zlength (live_2)) = n_pre) := NewPreH6
    simpa only [Zlength_replace_Znth] using PreH6

theorem proof_of_sort_entail_wit_14_split_goal_1 : sort_entail_wit_14_split_goal_1 := by
  unfold sort_entail_wit_14_split_goal_1
  intro input n_pre i bucket_starts live sorted_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH11 : (CountingSorted input sorted_2) := NewPreH12
    have PreH12 : (CountingCopyProgress input sorted_2 live i) := NewPreH13
    have he : i = Zlength input := by omega
    rw [he] at PreH12
    have hlive := counting_copy_complete__copyback input sorted_2 live (by omega) PreH12
    rw [hlive]
    dump_pre_spatial
    exact PreH11

theorem proof_of_sort_entail_wit_14_split_goal_spatial : sort_entail_wit_14_split_goal_spatial := by
  unfold sort_entail_wit_14_split_goal_spatial
  intro input n_pre i bucket_starts live sorted_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13
  have PreH2 : ((0 : Int) <= n_pre) := NewPreH2
  have PreH3 : (n_pre <= 100) := NewPreH3
  have hout : intArray.seg (&("output")) 0 n_pre sorted_2 ** intArray.undef_seg (&("output")) n_pre 100
      |-- intArray.undef_full (&("output")) 100 := by
    refine naive_C_Rules.toContext.derivable1_trans _ _ _
      (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
        (intArray.seg_to_undef_seg (&("output")) 0 n_pre sorted_2)
        (naive_C_Rules.toContext.derivable1_refl _)) ?_
    simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using
      intArray.undef_seg_merge_to_undef_full (&("output")) 0 n_pre 100 ⟨PreH2, PreH3⟩
  refine naive_C_Rules.toContext.derivable1_trans _
    ((intArray.seg (&("output")) 0 n_pre sorted_2 ** intArray.undef_seg (&("output")) n_pre 100) **
      intArray.full (&("count")) 100 bucket_starts) _ ?_ ?_
  · cancel
  · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ hout
      (intArray.full_to_undef_full (&("count")) 100 bucket_starts)


theorem proof_of_sort_return_wit_1_split_goal_1 : sort_return_wit_1_split_goal_1 := by
  unfold sort_return_wit_1_split_goal_1
  intro input n_pre sorted NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (CountingSorted input sorted) := NewPreH5
    exact PreH5.2

theorem proof_of_sort_return_wit_1_split_goal_2 : sort_return_wit_1_split_goal_2 := by
  unfold sort_return_wit_1_split_goal_2
  intro input n_pre sorted NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (CountingSorted input sorted) := NewPreH5
    exact PreH5.1

theorem proof_of_sort_safety_wit_10 : sort_safety_wit_10 := by
  unfold sort_safety_wit_10
  right
  intro input a_pre n_pre value positions output_mixed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have h0 := bounds_index positions 0 n_pre value PreH11 PreH12 ⟨by omega, by omega⟩
  have h1 := bounds_index positions 0 n_pre (value-1) PreH11 PreH12 ⟨by omega, by omega⟩
  have hb := PreH13 PreH1
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_sort_entail_wit_1 : sort_entail_wit_1 := by
  unfold sort_entail_wit_1
  right
  intro input n_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  have hnone : Forall (Eq (none : Option Int)) (List.replicate 100 (none : Option Int)) := by
    apply Forall.iff_forall_mem.mpr
    intro x hx
    exact (List.mem_replicate.mp hx).2.symm
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (List.replicate 100 (none : Option Int)) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (List.replicate 100 (none : Option Int)) ?_
  split_pure_spatial
  · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
      (intArray.undef_full_to_mixed_full (&("output")) 100)
      (intArray.undef_full_to_mixed_full (&("count")) 100)
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | assumption
      | decide
      | rfl
      | exact (fun k hk => Znth_repeat_lt (none : Option Int) 100 k none hk)
      | exact (fun value hv => False.elim (by omega))


theorem proof_of_sort_entail_wit_2 : sort_entail_wit_2 := by
  unfold sort_entail_wit_2
  right
  intro input n_pre value count_mixed_2 output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12
  have PreH1 : (value < 100) := NewPreH1
  have PreH2 : ((0 : Int) <= n_pre) := NewPreH2
  have PreH3 : (n_pre <= 100) := NewPreH3
  have PreH4 : ((Zlength (input)) = n_pre) := NewPreH4
  have PreH5 : ((Zlength (output_mixed_2)) = 100) := NewPreH5
  have PreH6 : ((Zlength (count_mixed_2)) = 100) := NewPreH6
  have PreH7 : ((0 : Int) <= value) := NewPreH7
  have PreH8 : (value <= 100) := NewPreH8
  have PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 100))) := by
    intro k hindex
    have value_PreH9 := annotation_Forall_nth _ input k 0 NewPreH9 (by omega)
    have value_PreH10 := annotation_Forall_nth _ input k 0 NewPreH10 (by omega)
    omega
  have PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 (none : Option Int)) = None)) := by
    intro k_2 hindex
    have value_PreH11 := annotation_Forall_nth _ output_mixed_2 k_2 none NewPreH11 (by rfl)
    exact value_PreH11.symm
  have PreH11 : (CountingZeroedPrefix count_mixed_2 value) := NewPreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_sort_entail_wit_2_split_goal_1 input n_pre value count_mixed_2 output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12
      | exact proof_of_sort_entail_wit_2_split_goal_2 input n_pre value count_mixed_2 output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12


theorem proof_of_sort_entail_wit_3 : sort_entail_wit_3 := by
  unfold sort_entail_wit_3
  right
  intro input n_pre value count_mixed output_mixed_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12
  let value_2 : Int := value
  have PreH6 : ((Zlength (count_mixed)) = 100) := NewPreH6
  have PreH11 : (CountingZeroedPrefix count_mixed value_2) := by first | assumption | omega
  have hm := counting_all_zero_materialization__initial_zeroing count_mixed PreH6
    (fun value hv => PreH11 value (by omega))
  subst count_mixed
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (List.replicate 100 (0 : Int)) ?_
  split_pure_spatial
  · exact intArray.mixed_full_to_full (&("count")) 100 (List.replicate 100 (0 : Int))
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | assumption
      | rfl
      | exact (fun value hv => Znth_repeat 0 100 value)
      | (apply Forall.iff_forall_mem.mpr; intro x hx; have he := (List.mem_replicate.mp hx).2; subst x; omega)
      | exact counting_histogram_empty__initial_zeroing input _ (fun value hv => Znth_repeat 0 100 value)


theorem proof_of_sort_entail_wit_4 : sort_entail_wit_4 := by
  unfold sort_entail_wit_4
  right
  intro input n_pre i output_mixed counts PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hv := value_bounds input i PreH13 PreH14 ⟨PreH11, by omega⟩
  have hc := bounds_index counts 0 i (Znth i input 0) PreH15 PreH16 ⟨hv.1, by omega⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_5 : sort_entail_wit_5 := by
  unfold sort_entail_wit_5
  right
  intro input n_pre i output_mixed_2 counts_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hc := bounds_index counts_2 0 i (Znth i input 0) PreH17 PreH18 ⟨PreH1, by omega⟩
  have hu : Forall (GE.ge (i+1)) counts_2 := forall_weaken PreH18 (by intro x hx; omega)
  have hl := forall_replace (LE.le (0 : Int)) 0 (Znth (Znth i input 0) counts_2 0+1) counts_2
    (Znth i input 0) ⟨PreH1, by omega⟩ PreH17 (by omega)
  have hh := forall_replace (GE.ge (i+1)) 0 (Znth (Znth i input 0) counts_2 0+1) counts_2
    (Znth i input 0) ⟨PreH1, by omega⟩ hu (by omega)
  have hp := proof_of_sort_entail_wit_5_split_goal_1 input n_pre i output_mixed_2 counts_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hlen := proof_of_sort_entail_wit_5_split_goal_4 input n_pre i output_mixed_2 counts_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_6 : sort_entail_wit_6 := by
  unfold sort_entail_wit_6
  right
  intro input n_pre i counts output_mixed_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hh : Forall (GE.ge n_pre) counts := by
    have hi : i = n_pre := by omega
    simpa only [hi] using PreH12
  have hc := proof_of_sort_entail_wit_6_split_goal_1 input n_pre i counts output_mixed_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hb := proof_of_sort_entail_wit_6_split_goal_2 input n_pre i counts output_mixed_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_7 : sort_entail_wit_7 := by
  unfold sort_entail_wit_7
  right
  intro input n_pre value positions_2 output_mixed_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hv := bounds_index positions_2 0 n_pre value PreH11 PreH12 ⟨by omega, by omega⟩
  have hp := bounds_index positions_2 0 n_pre (value-1) PreH11 PreH12 ⟨by omega, by omega⟩
  have hs := PreH13 PreH1
  have hl := forall_replace (LE.le (0 : Int)) 0
    (Znth value positions_2 0+Znth (value-1) positions_2 0) positions_2 value
    ⟨by omega, by omega⟩ PreH11 (by omega)
  have hh := forall_replace (GE.ge n_pre) 0
    (Znth value positions_2 0+Znth (value-1) positions_2 0) positions_2 value
    ⟨by omega, by omega⟩ PreH12 hs
  have hc := proof_of_sort_entail_wit_7_split_goal_1 input n_pre value positions_2 output_mixed_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hb := proof_of_sort_entail_wit_7_split_goal_2 input n_pre value positions_2 output_mixed_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hlen := proof_of_sort_entail_wit_7_split_goal_5 input n_pre value positions_2 output_mixed_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_8 : sort_entail_wit_8 := by
  unfold sort_entail_wit_8
  right
  intro input n_pre value positions_2 output_mixed_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have he : value = 100 := by omega
  subst value
  have hinput : ∀ x, In x input → 0 ≤ x ∧ x < 100 := by
    intro x hx; exact ⟨PreH9.mem hx, PreH10.mem hx⟩
  obtain ⟨sorted, hlen, hbounds, hsorted⟩ := counting_canonical_sorted_exists__placement_boundaries input hinput
  have hsl : Forall (LE.le (0 : Int)) sorted :=
    (indexed_Forall _ sorted 0).mpr (by intro k hk; exact (hbounds k (by omega)).1)
  have hsu : Forall (GT.gt (100 : Int)) sorted :=
    (indexed_Forall _ sorted 0).mpr (by intro k hk; exact (hbounds k (by omega)).2)
  have hplacement := counting_placement_initial__placement_boundaries input positions_2 output_mixed_2 sorted hsorted PreH15
  have hpositive : Zlength input-1 ≥ 0 → 1 ≤ Znth (Znth (Zlength input-1) input 0) positions_2 0 := by
    intro hn
    have hi : 0 ≤ Zlength input-1 ∧ Zlength input-1 < Zlength input := by omega
    have hv := value_bounds input (Zlength input-1) PreH9 PreH10 hi
    rw [PreH15 _ hv, if_pos hv.2]
    exact counting_cumulative_positive_at_In__placement_boundaries input _ hv.1 (nth_mem input _ hi)
  have hsuffix : Forall (Eq (none : Option Int)) (sublist (Zlength input) 100 output_mixed_2) := by
    apply Forall.iff_forall_mem.mpr
    intro x hx
    exact PreH14.mem (List.mem_of_mem_take (List.mem_of_mem_drop hx))
  Exists positions_2 sorted
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_9 : sort_entail_wit_9 := by
  unfold sort_entail_wit_9
  right
  intro input n_pre i output_mixed bucket_ends sorted positions PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hv := value_bounds input i PreH17 PreH18 ⟨PreH7, by omega⟩
  have hc := bounds_index positions 0 n_pre (Znth i input 0) PreH21 PreH22 ⟨hv.1, by omega⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_10 : sort_entail_wit_10 := by
  unfold sort_entail_wit_10
  right
  intro input n_pre i output_mixed bucket_ends sorted positions PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have he := Znth_replace_Znth_Same 0 positions (Znth i input 0)
    (Znth (Znth i input 0) positions 0-1) ⟨PreH5, by omega⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> rw [he] <;> omega

theorem proof_of_sort_entail_wit_11 : sort_entail_wit_11 := by
  unfold sort_entail_wit_11
  right
  intro input n_pre i output_mixed_2 bucket_ends_2 sorted_2 positions_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hbi : ∀ k, 0 ≤ k ∧ k < n_pre → 0 ≤ Znth k input 0 ∧ Znth k input 0 < 100 :=
    by intro k hk; exact value_bounds input k PreH21 PreH22 ⟨hk.1, by omega⟩
  have hbs : ∀ k, 0 ≤ k ∧ k < n_pre → 0 ≤ Znth k sorted_2 0 ∧ Znth k sorted_2 0 < 100 :=
    by intro k hk; exact value_bounds sorted_2 k PreH23 PreH24 ⟨hk.1, by omega⟩
  have hbp : ∀ k, 0 ≤ k ∧ k < 100 → 0 ≤ Znth k positions_2 0 ∧ Znth k positions_2 0 ≤ n_pre :=
    by intro k hk; exact bounds_index positions_2 0 n_pre k PreH25 PreH26 ⟨hk.1, by omega⟩
  have hbo : ∀ k, n_pre ≤ k ∧ k < 100 → Znth k output_mixed_2 none = none := by
    intro k hk
    exact ((forall_sublist_index (Eq (none : Option Int)) none output_mixed_2 n_pre 100
      ⟨PreH12, PreH13⟩ (by omega)).mp PreH28 k hk).symm
  have hstep := counting_placement_step__placement_transition n_pre input i output_mixed_2 bucket_ends_2 sorted_2 positions_2
    none ⟨PreH12, PreH13⟩ PreH14 PreH15 PreH16 PreH18 ⟨PreH11, PreH20⟩ hbi hbs hbp hbo PreH7 PreH29
  obtain ⟨hpositions, hpositive, hsuffix, hprogress⟩ := hstep
  let np := replace_Znth (Znth i input 0) (Znth (Znth i input 0) positions_2 0-1) positions_2
  let no := replace_Znth (Znth (Znth i input 0) np 0) (some (Znth i input 0)) output_mixed_2
  have hpl : Zlength np = 100 := by dsimp only [np]; rw [Zlength_replace_Znth]; exact PreH16
  have hol : Zlength no = 100 := by dsimp only [no]; rw [Zlength_replace_Znth]; exact PreH18
  have hpb := indexed_bounds np 0 (Zlength input) (by
    intro k hk; have hh : 0 ≤ Znth k np 0 ∧ Znth k np 0 ≤ n_pre := hpositions k ⟨hk.1, by omega⟩; exact ⟨hh.1, by omega⟩)
  have hos : Forall (Eq (none : Option Int)) (sublist (Zlength input) 100 no) := by
    apply (forall_sublist_index (Eq (none : Option Int)) none no (Zlength input) 100
      ⟨by omega, by omega⟩ (by omega)).mpr
    intro k hk; exact (hsuffix k ⟨by omega, hk.2⟩).symm
  Exists bucket_ends_2 sorted_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact hpb.1
      | exact hpb.2
      | exact hos
      | simpa only [Zlength_replace_Znth] using PreH16
      | simpa only [Zlength_replace_Znth] using PreH18
      | omega

theorem proof_of_sort_entail_wit_12 : sort_entail_wit_12 := by
  unfold sort_entail_wit_12
  right
  intro input n_pre i output_mixed bucket_ends positions sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have he : i = -1 := by omega
  subst i
  have hinput : ∀ x, In x input → 0 ≤ x ∧ x < 100 := by
    intro x hx; exact ⟨PreH11.mem hx, PreH12.mem hx⟩
  have hs := PreH19.1
  have hcomplete := counting_placement_complete__placement_boundaries input positions bucket_ends output_mixed sorted_2 hinput PreH19
  have hprefix := counting_output_prefix__placement_boundaries output_mixed sorted_2 n_pre
    (by omega) PreH5 (by intro k hk; exact hcomplete k ⟨hk.1, by omega⟩)
  have hc := counting_copy_initial__copyback input sorted_2
  Exists sorted_2
  split_pure_spatial
  · sep_apply (intArray.mixed_full_split_to_mixed_seg (&("output")) n_pre 100 output_mixed ⟨PreH2, PreH3⟩)
    rw [hprefix]
    sep_apply (intArray.mixed_seg_to_seg (&("output")) 0 n_pre sorted_2)
    sep_apply (intArray.mixed_seg_to_undef_seg (&("output")) n_pre 100 (sublist n_pre 100 output_mixed))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_13 : sort_entail_wit_13 := by
  unfold sort_entail_wit_13
  right
  intro input n_pre i bucket_starts_2 live_2 sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hc := proof_of_sort_entail_wit_13_split_goal_1 input n_pre i bucket_starts_2 live_2 sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hl := proof_of_sort_entail_wit_13_split_goal_2 input n_pre i bucket_starts_2 live_2 sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_14 : sort_entail_wit_14 := by
  unfold sort_entail_wit_14
  right
  intro input n_pre i bucket_starts live sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · exact proof_of_sort_entail_wit_14_split_goal_spatial input n_pre i bucket_starts live sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  · exact proof_of_sort_entail_wit_14_split_goal_1 input n_pre i bucket_starts live sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_sort_return_wit_1 : sort_return_wit_1 := by
  unfold sort_return_wit_1
  right
  intro input n_pre sorted NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  have PreH1 : ((0 : Int) <= n_pre) := NewPreH1
  have PreH2 : (n_pre <= 100) := NewPreH2
  have PreH3 : ((Zlength (input)) = n_pre) := NewPreH3
  have PreH4 : ((Zlength (sorted)) = n_pre) := NewPreH4
  have PreH5 : (CountingSorted input sorted) := NewPreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_sort_return_wit_1_split_goal_1 input n_pre sorted NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
      | exact proof_of_sort_return_wit_1_split_goal_2 input n_pre sorted NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5

end SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_proof_manual
