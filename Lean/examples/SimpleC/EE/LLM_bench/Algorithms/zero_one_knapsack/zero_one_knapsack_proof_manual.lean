import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_goal
import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open zero_one_knapsack_goal zero_one_knapsack_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray


attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

private theorem read_default (P : Int → Prop) (l : List Int) (k : Int)
    (h : Forall P l) (hd : P 0) : P (Znth k l 0) := by
  by_cases hi : k.toNat < l.length
  · have hp := h.mem (List.getElem_mem (l := l) hi)
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using hp
  · simpa only [Znth, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega : l.length ≤ k.toNat), Option.getD_none] using hd

private theorem read_in (P : Int → Prop) (l : List Int) (k : Int)
    (h : Forall P l) (hk : 0 ≤ k ∧ k < Zlength l) : P (Znth k l 0) := by
  have hi : k.toNat < l.length := by change 0 ≤ k ∧ k < (l.length : Int) at hk; omega
  have hp := h.mem (List.getElem_mem (l := l) hi)
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using hp

private theorem positive_nonnegative (l : List Int) (h : Forall (LE.le (1 : Int)) l) :
    Forall (LE.le (0 : Int)) l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx; have := h.mem hx; omega

private theorem forall_snoc {A : Type} {P : A → Prop} {l : List A} {x : A}
    (hl : Forall P l) (hx : P x) : Forall P (l ++ [x]) := by
  apply Forall.iff_forall_mem.mpr
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hl.mem ha
  · have he := List.mem_singleton.mp ha; subst a; exact hx

private theorem previous_cell (weights values dp : List Int) (capacity width i j col : Int)
    (hs : KnapsackRowProgress weights values capacity dp i j) (hi : 1 ≤ i)
    (hc : 0 ≤ capacity) (hw : width = capacity+1)
    (hcol : 0 ≤ col ∧ col ≤ capacity) (hcj : col ≤ j) :
    KnapsackCellCorrect weights values (i-1) col (Znth (((i-1)*width+col)-0) dp 0) := by
  have he : ((i-1)*width+col)-0 = KnapsackCellIndex capacity (i-1) col := by
    rw [hw]; simp [KnapsackCellIndex]
  rw [he]
  apply hs (i-1) col (by omega) hcol
  unfold KnapsackCellIndex
  constructor
  · exact add_nonneg (mul_nonneg (by omega) (by omega)) hcol.1
  · nlinarith

private theorem scratch_full_tail_undef (x k cap : Int) (l : List Int)
    (hk : 0 ≤ k ∧ k ≤ cap) :
    intArray.full x k l ** intArray.undef_seg x k cap |-- intArray.undef_full x cap := by
  sep_apply (intArray.full_to_undef_full x k l)
  sep_apply (intArray.undef_full_to_undef_seg x k)
  sep_apply (intArray.undef_seg_merge_to_undef_full x 0 k cap hk)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel

theorem proof_of_zeroOneKnapsack_safety_wit_22 : zeroOneKnapsack_safety_wit_22 := by
  unfold zeroOneKnapsack_safety_wit_22
  right
  intro values_l weights_l weights_pre values_pre n_pre capacity_pre dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  have hweights := PreH40
  have hvalues0 := PreH41
  have hvalues1 := PreH42
  have hrow := PreH45
  have hdp0 := PreH43
  have hdp1 := PreH44
  have hp0 := read_default _ dp_l (((i-1)*width+(j-Znth (i-1) weights_l 0))-0) hdp0 (by omega)
  have hp1 := read_default _ dp_l (((i-1)*width+(j-Znth (i-1) weights_l 0))-0) hdp1 (by omega)
  have hv0 := read_default _ values_l (i-1) hvalues0 (by omega)
  have hv1 := read_default _ values_l (i-1) hvalues1 (by omega)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MIN, INT_MAX] <;> omega

theorem proof_of_zeroOneKnapsack_entail_wit_1 : zeroOneKnapsack_entail_wit_1 := by
  unfold zeroOneKnapsack_entail_wit_1
  left
  intro values_l weights_l weights_pre values_pre n_pre capacity_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hweights := PreH7
  have hvalues0 := PreH9
  have hvalues1 := PreH10
  have hp : KnapsackRowsDone weights_l values_l capacity_pre [] 0 := by
    intro row col hr hc hi
    have hn : 0 ≤ KnapsackCellIndex capacity_pre row col := by
      unfold KnapsackCellIndex
      exact add_nonneg (mul_nonneg hr (by omega)) hc.1
    omega
  have htotal : 0 ≤ (n_pre+1)*(capacity_pre+1) ∧ (n_pre+1)*(capacity_pre+1) ≤ 90601 := by
    constructor <;> nlinarith
  sep_apply (intArray.undef_full_split_to_undef_seg (&("dp")) ((n_pre+1)*(capacity_pre+1)) 90601 htotal)
  Exists ([] : List Int)
  simp only [Int.zero_mul]
  have hemp : emp |-- intArray.seg (&("dp")) 0 0 [] := by
    refine naive_C_Rules.toContext.derivable1_trans _ ( “ ((0 : Int) = 0) ” && emp) _ ?_
      (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (intArray.seg_empty (&("dp")) 0 0)).2)
    split_pure_spatial
    · cancel
    · dump_pre_spatial; rfl
  split_pure_spatial
  · sep_apply_right hemp
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_2 : zeroOneKnapsack_entail_wit_2 := by
  unfold zeroOneKnapsack_entail_wit_2
  right
  intro values_l weights_l n_pre capacity_pre dp_l_2 i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hweights := PreH9
  have hvalues0 := PreH10
  have hvalues1 := PreH11
  have hdp0 := PreH12
  have hdp1 := PreH13
  have hrows := PreH14
  have hp := KnapsackRowsDone_to_RowProgress0 weights_l values_l capacity_pre dp_l_2 i (by omega) hrows
  Exists dp_l_2
  simp only [Int.add_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_3 : zeroOneKnapsack_entail_wit_3 := by
  unfold zeroOneKnapsack_entail_wit_3
  right
  intro values_l weights_l n_pre capacity_pre dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hweights := PreH23
  have hvalues0 := PreH24
  have hvalues1 := PreH25
  have hrow := PreH28
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_4 : zeroOneKnapsack_entail_wit_4 := by
  unfold zeroOneKnapsack_entail_wit_4
  right
  intro values_l weights_l n_pre capacity_pre dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hweights := PreH33
  have hvalues0 := PreH34
  have hvalues1 := PreH35
  have hrow := PreH38
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_5 : zeroOneKnapsack_entail_wit_5 := by
  unfold zeroOneKnapsack_entail_wit_5
  right
  intro values_l weights_l n_pre capacity_pre dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  have hweights := PreH38
  have hvalues0 := PreH39
  have hvalues1 := PreH40
  have hrow := PreH43
  have hw := read_default _ weights_l (i-1) (positive_nonnegative weights_l hweights) (by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_7 : zeroOneKnapsack_entail_wit_7 := by
  unfold zeroOneKnapsack_entail_wit_7
  right
  intro values_l weights_l n_pre capacity_pre dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hweights := PreH11
  have hvalues0 := PreH12
  have hvalues1 := PreH13
  have hdp0 := PreH14
  have hdp1 := PreH15
  have hrow := PreH16
  have hj : j = capacity_pre+1 := by omega
  have hw : width = capacity_pre+1 := by omega
  have hp := KnapsackRowProgress_end_to_RowsDone weights_l values_l capacity_pre dp_l_2 i j hj hrow
  have he : (i+1)*width = i*width+j := by nlinarith
  Exists dp_l_2
  rw [he]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_8 : zeroOneKnapsack_entail_wit_8 := by
  unfold zeroOneKnapsack_entail_wit_8
  right
  intro values_l weights_l n_pre capacity_pre dp_l_2 i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hweights := PreH9
  have hvalues0 := PreH10
  have hvalues1 := PreH11
  have hdp0 := PreH12
  have hdp1 := PreH13
  have hrows := PreH14
  have hi : i = n_pre+1 := by omega
  have hw : width = capacity_pre+1 := by omega
  have hr : KnapsackMaxValue weights_l values_l n_pre capacity_pre
      (Znth (n_pre*width+capacity_pre) dp_l_2 0) := by
    have he : n_pre*width+capacity_pre = KnapsackCellIndex capacity_pre n_pre capacity_pre := by rw [hw]; rfl
    rw [he]
    apply hrows n_pre capacity_pre (by omega) ⟨by omega, by omega⟩
    unfold KnapsackCellIndex
    constructor <;> nlinarith
  Exists dp_l_2
  subst i
  rw [hw]
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (intArray.undef_seg_empty (&("dp")) ((n_pre+1)*(capacity_pre+1)))).1)
  split_pure_spatial
  · sep_apply (intArray.seg_to_full (&("dp")) 0 ((n_pre+1)*(capacity_pre+1)) dp_l_2)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (simpa only [hw] using hr) | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_9 : zeroOneKnapsack_entail_wit_9 := by
  unfold zeroOneKnapsack_entail_wit_9
  right
  intro values_l weights_l n_pre capacity_pre dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  apply scratch_full_tail_undef
  constructor <;> nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_6_1 : zeroOneKnapsack_entail_wit_6_1 := by
  unfold zeroOneKnapsack_entail_wit_6_1
  left
  intro values_l weights_l weights_pre values_pre n_pre capacity_pre dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hweights := PreH24
  have hvalues0 := PreH25
  have hvalues1 := PreH26
  have hdp0 := PreH27
  have hdp1 := PreH28
  have hrow := PreH29
  prop_apply (intArray.full_Zlength weights_pre n_pre weights_l)
  Intros_p weights_length
  prop_apply (intArray.full_Zlength values_pre n_pre values_l)
  Intros_p values_length
  have hw : width = capacity_pre+1 := by omega
  let w := Znth (i-1) weights_l 0
  let v := Znth (i-1) values_l 0
  let without := Znth (((i-1)*width+j)-0) dp_l_2 0
  let prev := Znth (((i-1)*width+(j-w))-0) dp_l_2 0
  have hcell : KnapsackCellCorrect weights_l values_l i j 0 := by
    have hi : i = 0 := by omega
    rw [hi]; exact KnapsackCellCorrect_row0_zero weights_l values_l j (by omega) (by omega)
  have hv := KnapsackCellCorrect_value_bound weights_l values_l i j (0) n_pre values_length ⟨by omega, by omega⟩
    (by intro k hk; exact ⟨read_in _ values_l k hvalues0 ⟨hk.1, by omega⟩,
      read_in _ values_l k hvalues1 ⟨hk.1, by omega⟩⟩) hcell
  prop_apply (intArray.seg_Zlength (&("dp")) 0 (i*width+j+1) (dp_l_2 ++ [0]))
  Intros_p dp_written
  simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at dp_written
  have dp_length : Zlength dp_l_2 = i*(capacity_pre+1)+j := by nlinarith
  have hp := KnapsackRowProgress_append_cell_recurrence weights_l values_l capacity_pre dp_l_2 i j (0)
    ⟨by omega, by omega⟩ hrow dp_length hcell
  have hzero := forall_snoc hdp0 hv.1
  have hmax := forall_snoc hdp1 hv.2
  have he : i*width+(j+1) = i*width+j+1 := by omega
  Exists (dp_l_2 ++ [0])
  dsimp only [w, v, without, prev] at *
  rw [he]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_6_2 : zeroOneKnapsack_entail_wit_6_2 := by
  unfold zeroOneKnapsack_entail_wit_6_2
  left
  intro values_l weights_l weights_pre values_pre n_pre capacity_pre dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hweights := PreH25
  have hvalues0 := PreH26
  have hvalues1 := PreH27
  have hdp0 := PreH28
  have hdp1 := PreH29
  have hrow := PreH30
  prop_apply (intArray.full_Zlength weights_pre n_pre weights_l)
  Intros_p weights_length
  prop_apply (intArray.full_Zlength values_pre n_pre values_l)
  Intros_p values_length
  have hw : width = capacity_pre+1 := by omega
  let w := Znth (i-1) weights_l 0
  let v := Znth (i-1) values_l 0
  let without := Znth (((i-1)*width+j)-0) dp_l_2 0
  let prev := Znth (((i-1)*width+(j-w))-0) dp_l_2 0
  have hcell : KnapsackCellCorrect weights_l values_l i j 0 := by
    have hj : j = 0 := by omega
    rw [hj]
    exact KnapsackCellCorrect_col0_zero weights_l values_l i ⟨by omega, by omega⟩ (by omega)
      (by intro k hk; exact read_in _ weights_l k hweights ⟨hk.1, by omega⟩)
  have hv := KnapsackCellCorrect_value_bound weights_l values_l i j (0) n_pre values_length ⟨by omega, by omega⟩
    (by intro k hk; exact ⟨read_in _ values_l k hvalues0 ⟨hk.1, by omega⟩,
      read_in _ values_l k hvalues1 ⟨hk.1, by omega⟩⟩) hcell
  prop_apply (intArray.seg_Zlength (&("dp")) 0 (i*width+j+1) (dp_l_2 ++ [0]))
  Intros_p dp_written
  simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at dp_written
  have dp_length : Zlength dp_l_2 = i*(capacity_pre+1)+j := by nlinarith
  have hp := KnapsackRowProgress_append_cell_recurrence weights_l values_l capacity_pre dp_l_2 i j (0)
    ⟨by omega, by omega⟩ hrow dp_length hcell
  have hzero := forall_snoc hdp0 hv.1
  have hmax := forall_snoc hdp1 hv.2
  have he : i*width+(j+1) = i*width+j+1 := by omega
  Exists (dp_l_2 ++ [0])
  dsimp only [w, v, without, prev] at *
  rw [he]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_6_3 : zeroOneKnapsack_entail_wit_6_3 := by
  unfold zeroOneKnapsack_entail_wit_6_3
  left
  intro values_l weights_l weights_pre values_pre n_pre capacity_pre dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  have hweights := PreH41
  have hvalues0 := PreH42
  have hvalues1 := PreH43
  have hdp0 := PreH44
  have hdp1 := PreH45
  have hrow := PreH46
  prop_apply (intArray.full_Zlength weights_pre n_pre weights_l)
  Intros_p weights_length
  prop_apply (intArray.full_Zlength values_pre n_pre values_l)
  Intros_p values_length
  have hw : width = capacity_pre+1 := by omega
  let w := Znth (i-1) weights_l 0
  let v := Znth (i-1) values_l 0
  let without := Znth (((i-1)*width+j)-0) dp_l_2 0
  let prev := Znth (((i-1)*width+(j-w))-0) dp_l_2 0
  have wpos : 1 ≤ w := read_in _ weights_l (i-1) hweights ⟨by omega, by omega⟩
  have hwithout := previous_cell weights_l values_l dp_l_2 capacity_pre width i j j hrow
    (by omega) (by omega) hw ⟨by omega, by omega⟩ (by omega)
  have hprev := previous_cell weights_l values_l dp_l_2 capacity_pre width i j (j-w) hrow
    (by omega) (by omega) hw ⟨by omega, by omega⟩ (by omega)
  have hcell : KnapsackCellCorrect weights_l values_l i j (prev+v) := by
    have hs := KnapsackCellCorrect_take_better weights_l values_l (i-1) j w v without prev ⟨by omega, by omega⟩ (by omega) rfl rfl (by omega)
      (by intro k hk; have hh := read_in _ weights_l k hweights hk; omega) hwithout hprev (by omega)
    simpa only [Int.sub_add_cancel] using hs
  have hv := KnapsackCellCorrect_value_bound weights_l values_l i j (prev+v) n_pre values_length ⟨by omega, by omega⟩
    (by intro k hk; exact ⟨read_in _ values_l k hvalues0 ⟨hk.1, by omega⟩,
      read_in _ values_l k hvalues1 ⟨hk.1, by omega⟩⟩) hcell
  prop_apply (intArray.seg_Zlength (&("dp")) 0 (i*width+j+1) (dp_l_2 ++ [prev+v]))
  Intros_p dp_written
  simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at dp_written
  have dp_length : Zlength dp_l_2 = i*(capacity_pre+1)+j := by nlinarith
  have hp := KnapsackRowProgress_append_cell_recurrence weights_l values_l capacity_pre dp_l_2 i j (prev+v)
    ⟨by omega, by omega⟩ hrow dp_length hcell
  have hzero := forall_snoc hdp0 hv.1
  have hmax := forall_snoc hdp1 hv.2
  have he : i*width+(j+1) = i*width+j+1 := by omega
  Exists (dp_l_2 ++ [prev+v])
  dsimp only [w, v, without, prev] at *
  rw [he]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_6_4 : zeroOneKnapsack_entail_wit_6_4 := by
  unfold zeroOneKnapsack_entail_wit_6_4
  left
  intro values_l weights_l weights_pre values_pre n_pre capacity_pre dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  have hweights := PreH41
  have hvalues0 := PreH42
  have hvalues1 := PreH43
  have hdp0 := PreH44
  have hdp1 := PreH45
  have hrow := PreH46
  prop_apply (intArray.full_Zlength weights_pre n_pre weights_l)
  Intros_p weights_length
  prop_apply (intArray.full_Zlength values_pre n_pre values_l)
  Intros_p values_length
  have hw : width = capacity_pre+1 := by omega
  let w := Znth (i-1) weights_l 0
  let v := Znth (i-1) values_l 0
  let without := Znth (((i-1)*width+j)-0) dp_l_2 0
  let prev := Znth (((i-1)*width+(j-w))-0) dp_l_2 0
  have wpos : 1 ≤ w := read_in _ weights_l (i-1) hweights ⟨by omega, by omega⟩
  have hwithout := previous_cell weights_l values_l dp_l_2 capacity_pre width i j j hrow
    (by omega) (by omega) hw ⟨by omega, by omega⟩ (by omega)
  have hprev := previous_cell weights_l values_l dp_l_2 capacity_pre width i j (j-w) hrow
    (by omega) (by omega) hw ⟨by omega, by omega⟩ (by omega)
  have hcell : KnapsackCellCorrect weights_l values_l i j without := by
    have hs := KnapsackCellCorrect_keep_without_when_better_or_equal weights_l values_l (i-1) j w v without prev ⟨by omega, by omega⟩ (by omega) rfl rfl (by omega)
      (by intro k hk; have hh := read_in _ weights_l k hweights hk; omega) hwithout hprev (by omega)
    simpa only [Int.sub_add_cancel] using hs
  have hv := KnapsackCellCorrect_value_bound weights_l values_l i j (without) n_pre values_length ⟨by omega, by omega⟩
    (by intro k hk; exact ⟨read_in _ values_l k hvalues0 ⟨hk.1, by omega⟩,
      read_in _ values_l k hvalues1 ⟨hk.1, by omega⟩⟩) hcell
  prop_apply (intArray.seg_Zlength (&("dp")) 0 (i*width+j+1) (dp_l_2 ++ [without]))
  Intros_p dp_written
  simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at dp_written
  have dp_length : Zlength dp_l_2 = i*(capacity_pre+1)+j := by nlinarith
  have hp := KnapsackRowProgress_append_cell_recurrence weights_l values_l capacity_pre dp_l_2 i j (without)
    ⟨by omega, by omega⟩ hrow dp_length hcell
  have hzero := forall_snoc hdp0 hv.1
  have hmax := forall_snoc hdp1 hv.2
  have he : i*width+(j+1) = i*width+j+1 := by omega
  Exists (dp_l_2 ++ [without])
  dsimp only [w, v, without, prev] at *
  rw [he]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_6_5 : zeroOneKnapsack_entail_wit_6_5 := by
  unfold zeroOneKnapsack_entail_wit_6_5
  left
  intro values_l weights_l weights_pre values_pre n_pre capacity_pre dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hweights := PreH36
  have hvalues0 := PreH37
  have hvalues1 := PreH38
  have hdp0 := PreH39
  have hdp1 := PreH40
  have hrow := PreH41
  prop_apply (intArray.full_Zlength weights_pre n_pre weights_l)
  Intros_p weights_length
  prop_apply (intArray.full_Zlength values_pre n_pre values_l)
  Intros_p values_length
  have hw : width = capacity_pre+1 := by omega
  let w := Znth (i-1) weights_l 0
  let v := Znth (i-1) values_l 0
  let without := Znth (((i-1)*width+j)-0) dp_l_2 0
  let prev := Znth (((i-1)*width+(j-w))-0) dp_l_2 0
  have wpos : 1 ≤ w := read_in _ weights_l (i-1) hweights ⟨by omega, by omega⟩
  have hwithout := previous_cell weights_l values_l dp_l_2 capacity_pre width i j j hrow
    (by omega) (by omega) hw ⟨by omega, by omega⟩ (by omega)
  have hcell : KnapsackCellCorrect weights_l values_l i j without := by
    have hs := KnapsackCellCorrect_too_heavy weights_l values_l (i-1) j w v without ⟨by omega, by omega⟩ (by omega) rfl rfl (by omega)
      (by intro k hk; have hh := read_in _ weights_l k hweights hk; omega) hwithout
    simpa only [Int.sub_add_cancel] using hs
  have hv := KnapsackCellCorrect_value_bound weights_l values_l i j (without) n_pre values_length ⟨by omega, by omega⟩
    (by intro k hk; exact ⟨read_in _ values_l k hvalues0 ⟨hk.1, by omega⟩,
      read_in _ values_l k hvalues1 ⟨hk.1, by omega⟩⟩) hcell
  prop_apply (intArray.seg_Zlength (&("dp")) 0 (i*width+j+1) (dp_l_2 ++ [without]))
  Intros_p dp_written
  simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at dp_written
  have dp_length : Zlength dp_l_2 = i*(capacity_pre+1)+j := by nlinarith
  have hp := KnapsackRowProgress_append_cell_recurrence weights_l values_l capacity_pre dp_l_2 i j (without)
    ⟨by omega, by omega⟩ hrow dp_length hcell
  have hzero := forall_snoc hdp0 hv.1
  have hmax := forall_snoc hdp1 hv.2
  have he : i*width+(j+1) = i*width+j+1 := by omega
  Exists (dp_l_2 ++ [without])
  dsimp only [w, v, without, prev] at *
  rw [he]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact Forall.nil
      | (solve | simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.sub_zero] at *; nlinarith)
      | nlinarith

end SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_proof_manual
