import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_goal
import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open energy_necklace_goal energy_necklace_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem app_nth (l : List Int) (x i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    Znth i (l++[x]) 0 = Znth i l 0 := ListLib.app_Znth1 0 l [x] i hi


private theorem nth_property (P : Int → Prop) (l : List Int) (i : Int)
    (h : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l 0) := by
  apply h.mem
  unfold Znth
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega)]
  simp only [Option.getD_some]
  exact List.getElem_mem _

private theorem forall_of_nth (P : Int → Prop) (l : List Int)
    (h : ∀ i, (0 ≤ i ∧ i < Zlength l) → P (Znth i l 0)) : Forall P l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
  have hp := h (i : Int) ⟨by omega, by simp only [Zlength, Int.ofNat_eq_coe]; omega⟩
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he] using hp

private theorem plan_nonnegative (vals : List Int) (left right energy : Int)
    (hv : Forall (fun x : Int => 0 ≤ x) vals) (hp : EnergyIntervalPlan vals left right energy) : 0 ≤ energy := by
  induction hp with
  | EnergyIntervalPlan_single => omega
  | EnergyIntervalPlan_merge l k r el er hl hk hr hpl hpr ihl ihr =>
    have h1 := nth_property _ vals l hv (by omega)
    have h2 := nth_property _ vals (k+1) hv (by omega)
    have h3 := nth_property _ vals (r+1) hv (by omega)
    exact add_nonneg (add_nonneg ihl ihr) (mul_nonneg (mul_nonneg h1 h2) h3)

private theorem plan_extend_right (vals : List Int) (left right energy : Int)
    (hv : Forall (fun x : Int => 0 ≤ x) vals) (hlr : 0 ≤ left ∧ left ≤ right)
    (hp : EnergyIntervalPlan vals left right energy) (extra : Nat)
    (hend : right + (extra : Int) + 1 < Zlength vals) :
    ∃ larger, energy ≤ larger ∧ EnergyIntervalPlan vals left (right + (extra : Int)) larger := by
  induction extra with
  | zero => exact ⟨energy,le_refl _,by simpa using hp⟩
  | succ m ih =>
    obtain ⟨larger,hle,hplan⟩ := ih (by omega)
    have hsingle : EnergyIntervalPlan vals (right+(m:Int)+1) (right+(m:Int)+1) 0 :=
      EnergyIntervalPlan_single _ (by omega) (by omega)
    have hm := EnergyIntervalPlan_merge left (right+(m:Int)) (right+(m:Int)+1) larger 0 hlr.1 (by omega) (by omega) hplan hsingle
    have h1 := nth_property _ vals left hv (by omega)
    have h2 := nth_property _ vals (right+(m:Int)+1) hv (by omega)
    have h3 := nth_property _ vals (right+(m:Int)+1+1) hv (by omega)
    refine ⟨larger + 0 + Znth left vals 0 * Znth (right+(m:Int)+1) vals 0 * Znth (right+(m:Int)+1+1) vals 0,?_,?_⟩
    · have := mul_nonneg (mul_nonneg h1 h2) h3; omega
    · simpa only [Nat.cast_add,Nat.cast_one,Int.add_assoc] using hm

private theorem plan_extend_left (vals : List Int) (left right energy : Int)
    (hv : Forall (fun x : Int => 0 ≤ x) vals) (hlr : left ≤ right)
    (hr : right+1 < Zlength vals) (hp : EnergyIntervalPlan vals left right energy)
    (extra : Nat) (he : (extra : Int) ≤ left) :
    ∃ larger, energy ≤ larger ∧ EnergyIntervalPlan vals (left-(extra:Int)) right larger := by
  induction extra with
  | zero => exact ⟨energy,le_refl _,by simpa using hp⟩
  | succ m ih =>
    obtain ⟨larger,hle,hplan⟩ := ih (by omega)
    have hsingle : EnergyIntervalPlan vals (left-((m+1:Nat):Int)) (left-((m+1:Nat):Int)) 0 :=
      EnergyIntervalPlan_single _ (by omega) (by omega)
    have hnext : left-((m+1:Nat):Int)+1 = left-(m:Int) := by omega
    have hm := EnergyIntervalPlan_merge (left-((m+1:Nat):Int)) (left-((m+1:Nat):Int)) right 0 larger (by omega) (by omega) hr hsingle (by rw [hnext]; exact hplan)
    have h1 := nth_property _ vals (left-((m+1:Nat):Int)) hv (by omega)
    have h2 := nth_property _ vals (left-((m+1:Nat):Int)+1) hv (by omega)
    have h3 := nth_property _ vals (right+1) hv (by omega)
    refine ⟨_,?_,hm⟩
    have := mul_nonneg (mul_nonneg h1 h2) h3; omega

private theorem plan_bounded_by_rotations (beads vals : List Int) (n bound left right energy : Int)
    (hn : 1 ≤ n) (hd : EnergyValsDuplicated beads vals n)
    (hv : Forall (fun x : Int => 0 ≤ x) vals)
    (hb : ∀ start e, (0 ≤ start ∧ start < n) → EnergyIntervalPlan vals start (start+n-1) e → e ≤ bound)
    (hlr : 0 ≤ left ∧ left ≤ right) (hlen : right-left+1 ≤ n)
    (hr : right+1 < Zlength vals) (hp : EnergyIntervalPlan vals left right energy) :
    0 ≤ energy ∧ energy ≤ bound := by
  have hen := plan_nonnegative vals left right energy hv hp
  have hvlen := hd.2.2.1
  let start := min left (n-1)
  have hs : (0 ≤ start ∧ start < n) ∧ start ≤ left ∧ right ≤ start+n-1 := by dsimp [start]; omega
  have he : ((left-start).toNat : Int) = left-start := by omega
  obtain ⟨e1,h1,hp1⟩ := plan_extend_left vals left right energy hv hlr.2 hr hp (left-start).toNat (by omega)
  rw [he] at hp1
  have hcancel : left-(left-start)=start := by omega
  rw [hcancel] at hp1
  have he2 : ((start+n-1-right).toNat : Int) = start+n-1-right := by omega
  obtain ⟨e2,h2,hp2⟩ := plan_extend_right vals start right e1 hv ⟨hs.1.1,by omega⟩ hp1 (start+n-1-right).toNat (by omega)
  rw [he2] at hp2
  have hcancel2 : right+(start+n-1-right)=start+n-1 := by omega
  rw [hcancel2] at hp2
  have := hb start e2 hs.1 hp2
  exact ⟨hen,by omega⟩

private theorem best_plan (vals : List Int) (left right ans : Int)
    (h : EnergyIntervalBest vals left right ans) : EnergyIntervalPlan vals left right ans := by
  obtain ⟨winner,⟨hp,hm⟩,he⟩ := h
  dsimp at he
  rw [← he]
  exact hp

private theorem duplicated_nonnegative (beads vals : List Int) (n : Int)
    (hd : EnergyValsDuplicated beads vals n) (hl : EnergyLabelsBounded beads n) :
    Forall (fun x : Int => 0 ≤ x) vals := by
  apply forall_of_nth
  intro i hi
  have := EnergyValsDuplicated_label_bound__arithmetic_safety_bounds beads vals n i hd hl (by have := hd.2.2.1; omega)
  omega

private theorem split_arithmetic (beads vals dp : List Int) (n total width len left right split : Int)
    (hn : 1 ≤ n) (ht : total=2*n) (hw : width=total)
    (hd : EnergyValsDuplicated beads vals n) (hl : EnergyLabelsBounded beads n)
    (hb : ∀ start e, (0 ≤ start ∧ start<n) → EnergyIntervalPlan vals start (start+n-1) e → e ≤ 2100000000)
    (hlen : 2 ≤ len ∧ len ≤ n) (hlr : 0 ≤ left ∧ left < total-len)
    (hr : right=left+len-1) (hs : left ≤ split ∧ split < right)
    (hcomplete : EnergyLengthsComplete vals dp width len) :
    EnergySplitArithmeticBounded vals dp width left right split 2100000000 := by
  have hvlen := hd.2.2.1
  have hv := duplicated_nonnegative beads vals n hd hl
  have hleft := hcomplete (split-left+1) left split (EnergyCellIndex width left split) ⟨by omega,by omega⟩ (by omega) rfl hlr.1 (by omega)
  have hright := hcomplete (right-split) (split+1) right (EnergyCellIndex width (split+1) right) ⟨by omega,by omega⟩ (by omega) rfl (by omega) (by omega)
  have hpl := best_plan _ _ _ _ hleft
  have hpr := best_plan _ _ _ _ hright
  have hel := plan_nonnegative _ _ _ _ hv hpl
  have her := plan_nonnegative _ _ _ _ hv hpr
  have hm := EnergyIntervalPlan_merge left split right _ _ hlr.1 hs (by omega) hpl hpr
  have htotal := plan_bounded_by_rotations beads vals n 2100000000 left right _ hn hd hv hb ⟨hlr.1,by omega⟩ (by omega) (by omega) hm
  have h1 := nth_property _ vals left hv (by omega)
  have h2 := nth_property _ vals (split+1) hv (by omega)
  have h3 := nth_property _ vals (right+1) hv (by omega)
  have hg := mul_nonneg (mul_nonneg h1 h2) h3
  dsimp only [EnergySplitArithmeticBounded]
  omega

theorem proof_of_energyNecklace_safety_wit_25 : energyNecklace_safety_wit_25 := by
  right
  intro n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48
  have hl : EnergyLabelsBounded beads_l n_pre := ⟨by assumption,fun idx hi => ⟨nth_property _ _ _ PreH46 (by omega),nth_property _ _ _ PreH47 (by omega)⟩⟩
  have hb0 := EnergyValsDuplicated_label_bound__arithmetic_safety_bounds beads_l vals_l n_pre left PreH29 hl (by omega)
  have hb1 := EnergyValsDuplicated_label_bound__arithmetic_safety_bounds beads_l vals_l n_pre (split+1) PreH29 hl (by omega)
  have hb2 := EnergyValsDuplicated_label_bound__arithmetic_safety_bounds beads_l vals_l n_pre (right+1) PreH29 hl (by omega)
  have hp : 0 ≤ Znth left vals_l 0 * Znth (split+1) vals_l 0 ∧ Znth left vals_l 0 * Znth (split+1) vals_l 0 ≤ 1000000 := by constructor <;> nlinarith [mul_nonneg (by omega : 0 ≤ Znth left vals_l 0) (by omega : 0 ≤ Znth (split+1) vals_l 0), mul_le_mul_of_nonneg_left hb1.2 (by omega : 0 ≤ Znth left vals_l 0)]
  have ht : 0 ≤ Znth left vals_l 0 * Znth (split+1) vals_l 0 * Znth (right+1) vals_l 0 ∧ Znth left vals_l 0 * Znth (split+1) vals_l 0 * Znth (right+1) vals_l 0 ≤ 1000000000 := by constructor <;> nlinarith [mul_nonneg hp.1 (by omega : 0 ≤ Znth (right+1) vals_l 0), mul_le_mul_of_nonneg_left hb2.2 hp.1]
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX,INT_MIN]; omega

theorem proof_of_energyNecklace_safety_wit_27 : energyNecklace_safety_wit_27 := by
  right
  intro n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48
  have hl : EnergyLabelsBounded beads_l n_pre := ⟨by assumption,fun idx hi => ⟨nth_property _ _ _ PreH46 (by omega),nth_property _ _ _ PreH47 (by omega)⟩⟩
  have hb0 := EnergyValsDuplicated_label_bound__arithmetic_safety_bounds beads_l vals_l n_pre left PreH29 hl (by omega)
  have hb1 := EnergyValsDuplicated_label_bound__arithmetic_safety_bounds beads_l vals_l n_pre (split+1) PreH29 hl (by omega)
  have hp : 0 ≤ Znth left vals_l 0 * Znth (split+1) vals_l 0 ∧ Znth left vals_l 0 * Znth (split+1) vals_l 0 ≤ 1000000 := by constructor <;> nlinarith [mul_nonneg (by omega : 0 ≤ Znth left vals_l 0) (by omega : 0 ≤ Znth (split+1) vals_l 0), mul_le_mul_of_nonneg_left hb1.2 (by omega : 0 ≤ Znth left vals_l 0)]
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX,INT_MIN]; omega

theorem proof_of_energyNecklace_safety_wit_31 : energyNecklace_safety_wit_31 := by
  right
  intro n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48
  have hl : EnergyLabelsBounded beads_l n_pre := ⟨by assumption,fun idx hi => ⟨nth_property _ _ _ PreH46 (by omega),nth_property _ _ _ PreH47 (by omega)⟩⟩
  have hb := split_arithmetic beads_l vals_l dp_l n_pre total width len left right split (by omega) PreH1 PreH2 PreH29 hl (fun start e hs hp => PreH48 vals_l start e ⟨⟨⟨PreH29,hs.1⟩,hs.2⟩,hp⟩) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH11 ⟨by omega,by omega⟩ PreH35
  dsimp only [EnergySplitArithmeticBounded,EnergyCellIndex] at hb
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX,INT_MIN]; omega

theorem proof_of_energyNecklace_safety_wit_32 : energyNecklace_safety_wit_32 := by
  right
  intro n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48
  have hl : EnergyLabelsBounded beads_l n_pre := ⟨by assumption,fun idx hi => ⟨nth_property _ _ _ PreH46 (by omega),nth_property _ _ _ PreH47 (by omega)⟩⟩
  have hb := split_arithmetic beads_l vals_l dp_l n_pre total width len left right split (by omega) PreH1 PreH2 PreH29 hl (fun start e hs hp => PreH48 vals_l start e ⟨⟨⟨PreH29,hs.1⟩,hs.2⟩,hp⟩) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH11 ⟨by omega,by omega⟩ PreH35
  dsimp only [EnergySplitArithmeticBounded,EnergyCellIndex] at hb
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX,INT_MIN]; omega

theorem proof_of_energyNecklace_entail_wit_8 : energyNecklace_entail_wit_8 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hp : EnergyLeftComplete vals_l_2 dp_l_2 width len 0 := by intro l r idx hl; omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_9 : energyNecklace_entail_wit_9 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hp : EnergySplitBest vals_l_2 dp_l_2 width len left left 0 := Or.inl ⟨rfl,rfl⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_10 : energyNecklace_entail_wit_10 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 best split right left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_11 : energyNecklace_entail_wit_11 := by
  right
  intro n_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48
  have hl : EnergyLabelsBounded beads_l n_pre := ⟨by assumption,fun idx hi => ⟨nth_property _ _ _ PreH46 (by omega),nth_property _ _ _ PreH47 (by omega)⟩⟩
  have hb := split_arithmetic beads_l vals_l dp_l n_pre total width len left right split (by omega) PreH1 PreH2 PreH29 hl (fun start e hs hp => PreH48 vals_l start e ⟨⟨⟨PreH29,hs.1⟩,hs.2⟩,hp⟩) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH11 ⟨by omega,by omega⟩ PreH35
  dsimp only [EnergySplitArithmeticBounded,EnergyCellIndex] at hb
  rw [PreH2,PreH11] at hb
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_12_1 : energyNecklace_entail_wit_12_1 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width len left right split left_value right_value gain candidate best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  have hd : EnergyLenDone vals_l_2 dp_l_2 total width len := ⟨by omega,by assumption,by assumption,by assumption,by omega,PreH32⟩
  have hlp : EnergyLeftProgress vals_l_2 dp_l_2 total width len left := ⟨hd,by omega,by omega,PreH35⟩
  have hsp : EnergySplitProgress vals_l_2 dp_l_2 total width len left split best := ⟨hlp,by omega,by omega,by omega,rfl,⟨by omega,by omega⟩,⟨by omega,by omega⟩,PreH41⟩
  have hc : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate := ⟨⟨PreH13,PreH14⟩,by omega,by dsimp only [EnergyCellIndex]; rw [PreH21,PreH18,PreH19,PreH20]⟩
  have hx := EnergySplitProgress_step_take__dp_interval_progress vals_l_2 dp_l_2 total width len left right split best candidate PreH12 ⟨PreH13,PreH14⟩ hsp hc ⟨PreH22,PreH23⟩ PreH1
  have hp : EnergySplitBest vals_l_2 dp_l_2 width len left (split+1) candidate := hx.2.2.2.2.2.2.2
  rw [PreH3,PreH21] at hp
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_12_2 : energyNecklace_entail_wit_12_2 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width len left right split left_value right_value gain candidate best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  have hd : EnergyLenDone vals_l_2 dp_l_2 total width len := ⟨by omega,by assumption,by assumption,by assumption,by omega,PreH32⟩
  have hlp : EnergyLeftProgress vals_l_2 dp_l_2 total width len left := ⟨hd,by omega,by omega,PreH35⟩
  have hsp : EnergySplitProgress vals_l_2 dp_l_2 total width len left split best := ⟨hlp,by omega,by omega,by omega,rfl,⟨by omega,by omega⟩,⟨by omega,by omega⟩,PreH41⟩
  have hc : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate := ⟨⟨PreH13,PreH14⟩,by omega,by dsimp only [EnergyCellIndex]; rw [PreH21,PreH18,PreH19,PreH20]⟩
  have hx := EnergySplitProgress_step_keep__dp_interval_progress vals_l_2 dp_l_2 total width len left right split best candidate PreH12 ⟨PreH13,PreH14⟩ hsp hc PreH22 PreH1
  have hp : EnergySplitBest vals_l_2 dp_l_2 width len left (split+1) best := hx.2.2.2.2.2.2.2
  rw [PreH3] at hp
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width len left right split left_value right_value gain candidate best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 best split right left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have hd : EnergyLenDone vals_l_2 dp_l_2 total width len := ⟨by omega,by assumption,by assumption,by assumption,by omega,PreH29⟩
  have hlp : EnergyLeftProgress vals_l_2 dp_l_2 total width len left := ⟨hd,by omega,by omega,PreH32⟩
  have hsp : EnergySplitProgress vals_l_2 dp_l_2 total width len left split best := ⟨hlp,by omega,by omega,by omega,rfl,⟨by omega,by omega⟩,⟨by omega,by omega⟩,PreH38⟩
  have hm := EnergySplitProgress_finish_interval_best__dp_interval_progress vals_l_2 dp_l_2 total width len left right split best PreH12 PreH1 (by omega) hsp
  have he : split = left+len-1 := by omega
  rw [PreH12] at hm
  have hp := PreH38
  rw [he] at hp
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width len left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have hd : EnergyLenDone vals_l_2 dp_l_2 total width len := ⟨by omega,by assumption,by assumption,by assumption,by omega,PreH25⟩
  have hlp : EnergyLeftProgress vals_l_2 dp_l_2 total width len left := ⟨hd,by omega,by omega,PreH28⟩
  have hsp : EnergySplitProgress vals_l_2 dp_l_2 total width len left right best := ⟨hlp,by omega,by omega,by omega,rfl,⟨by omega,by omega⟩,⟨by omega,by omega⟩,PreH34⟩
  have hx := EnergyLeftProgress_step_update__dp_interval_progress vals_l_2 dp_l_2 total width len left right best PreH11 PreH9 PreH10 hsp PreH35
  have hp : EnergyLeftComplete vals_l_2 (replace_Znth (EnergyCellIndex width left right) best dp_l_2) width len (left+1) := hx.2.2.2
  have hdnew : EnergyLengthsComplete vals_l_2 (replace_Znth (EnergyCellIndex width left right) best dp_l_2) width len := hx.1.2.2.2.2.2
  dsimp only [EnergyCellIndex] at hp hdnew
  rw [PreH2,PreH11] at hp hdnew
  have hlen : Zlength dp_l_2 = (2*n_pre)*total := by rw [PreH18,PreH1,PreH2,PreH1]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hd : EnergyLenDone vals_l_2 dp_l_2 total width len := ⟨by omega,by assumption,by assumption,by assumption,by omega,PreH20⟩
  have hlp : EnergyLeftProgress vals_l_2 dp_l_2 total width len left := ⟨hd,by omega,by omega,PreH23⟩
  have hx := EnergyLeftProgress_finish_len__dp_interval_progress vals_l_2 dp_l_2 total width len left PreH1 PreH11 hlp
  have hp : EnergyLengthsComplete vals_l_2 dp_l_2 width (len+1) := hx.2.2.2.2.2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_17 : energyNecklace_entail_wit_17 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have he : len=n_pre+1 := by omega
  have hp : EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre+1) := by simpa only [he] using PreH18
  have ha : EnergyAnswerBest vals_l_2 n_pre 0 0 := Or.inl ⟨rfl,rfl⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_18 : energyNecklace_entail_wit_18 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hp : EnergyIntervalBest vals_l_2 start (start+n_pre-1) (Znth (start*width+start+n_pre-1) dp_l_2 0) := PreH20 n_pre start (start+n_pre-1) _ ⟨by omega,by omega⟩ rfl (by dsimp only [EnergyCellIndex]; ring) PreH8 (by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19 := by
  right
  intro n_pre beads_l vals_l_2 dp_l total width start answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hl : EnergyLabelsBounded beads_l n_pre := ⟨by assumption,fun idx hi => ⟨nth_property _ _ _ PreH30 (by omega),nth_property _ _ _ PreH31 (by omega)⟩⟩
  have hv := duplicated_nonnegative beads_l vals_l_2 n_pre PreH13 hl
  have hp := best_plan _ _ _ _ PreH28
  have hlo := plan_nonnegative _ _ _ _ hv hp
  have hhi := PreH32 vals_l_2 start _ ⟨⟨⟨PreH13,PreH7⟩,PreH8⟩,hp⟩
  rw [PreH2] at hlo hhi
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_20_1 : energyNecklace_entail_wit_20_1 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width start value answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hp : EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer := ⟨PreH15,by assumption,by assumption,⟨by omega,by omega⟩,⟨by omega,by omega⟩,PreH29⟩
  have hx := EnergyAnswerProgress_step_update__answer_loop beads_l vals_l_2 dp_l_2 n_pre total width start answer value hp ⟨by omega,by omega⟩ PreH30 ⟨by omega,by omega⟩ PreH1
  have ha : EnergyAnswerBest vals_l_2 n_pre (start+1) value := hx.2.2.2.2.2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_20_2 : energyNecklace_entail_wit_20_2 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width start value answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hp : EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer := ⟨PreH15,by assumption,by assumption,⟨by omega,by omega⟩,⟨by omega,by omega⟩,PreH29⟩
  have hx := EnergyAnswerProgress_step_keep__answer_loop beads_l vals_l_2 dp_l_2 n_pre total width start answer value hp ⟨by omega,by omega⟩ PreH30 (by omega) PreH1
  have ha : EnergyAnswerBest vals_l_2 n_pre (start+1) answer := hx.2.2.2.2.2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_21 : energyNecklace_entail_wit_21 := by
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width start_2 value answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; omega) | nlinarith

private theorem forall2_eq {xs ys : List Int} (h : Forall2 Eq xs ys) : xs=ys := by
  induction h with
  | nil => rfl
  | cons he ht ih => cases he; cases ih; rfl

private theorem forall2_refl (xs : List Int) : Forall2 Eq xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons rfl ih

private theorem view_get (xs ys : List Int) (off len k : Int)
    (hoff : 0 ≤ off) (hk : 0 ≤ k ∧ k < len)
    (hv : Forall2 Eq (sublist off (off+len) xs) (sublist 0 len ys)) :
    Znth (off+k) xs 0 = Znth k ys 0 := by
  have h := congrArg (fun l => Znth k l 0) (forall2_eq hv)
  change Znth k (sublist off (off+len) xs) 0 = Znth k (sublist 0 len ys) 0 at h
  rw [Znth_sublist 0 off k (off+len) xs hoff (by omega), Znth_sublist 0 0 k len ys (by omega) (by omega)] at h
  simpa only [Int.add_zero,Int.add_comm] using h

private theorem view_make (xs ys : List Int) (off len : Int)
    (hoff : 0 ≤ off) (hlen : 0 ≤ len) (hx : off+len ≤ Zlength xs) (hy : len ≤ Zlength ys)
    (h : ∀ k, (0 ≤ k ∧ k<len) → Znth (off+k) xs 0 = Znth k ys 0) :
    Forall2 Eq (sublist off (off+len) xs) (sublist 0 len ys) := by
  have he : sublist off (off+len) xs = sublist 0 len ys := by
    apply (ListLib.list_eq_ext _ _ 0).mpr
    have hlx : Zlength (sublist off (off+len) xs) = len := by
      simp only [Zlength,sublist_length off (off+len) xs (by omega) hx,Int.ofNat_eq_coe]; omega
    have hly : Zlength (sublist 0 len ys) = len := by
      simp only [Zlength,sublist_length 0 len ys (by omega) hy,Int.ofNat_eq_coe]; omega
    constructor
    · change Zlength (sublist off (off+len) xs) = Zlength (sublist 0 len ys); omega
    · change ∀ k, (0 ≤ k ∧ k<Zlength (sublist off (off+len) xs)) → Znth k (sublist off (off+len) xs) 0 = Znth k (sublist 0 len ys) 0
      intro k hk
      rw [Znth_sublist 0 off k (off+len) xs hoff (by omega),Znth_sublist 0 0 k len ys (by omega) (by omega)]
      simpa only [Int.add_zero,Int.add_comm] using h k (by omega)
  rw [he]
  exact forall2_refl _

private theorem prefix_view_make (xs ys : List Int) (len : Int)
    (hlen : 0 ≤ len) (hx : len ≤ Zlength xs) (hy : len ≤ Zlength ys)
    (h : ∀ k, (0 ≤ k ∧ k<len) → Znth k xs 0 = Znth k ys 0) :
    Forall2 Eq (sublist 0 len xs) (sublist 0 len ys) := by
  simpa only [Int.zero_add] using view_make xs ys 0 len (by omega) hlen (by omega) hy (by simpa only [Int.zero_add] using h)

attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg

private theorem scratch_cleanup (a len total : Int) (l : List Int) (hc : 0 ≤ len ∧ len ≤ total) :
    intArray.full a len l ** intArray.undef_seg a len total |-- intArray.undef_full a total := by
  refine naive_C_Rules.toContext.derivable1_trans _ (intArray.undef_seg a 0 len ** intArray.undef_seg a len total) _ ?_ ?_
  · apply naive_C_Rules.toContext.derivable1_sepcon_mono
    · exact naive_C_Rules.toContext.derivable1_trans _ _ _ (intArray.full_to_seg a len l) (intArray.seg_to_undef_seg a 0 len l)
    · exact naive_C_Rules.toContext.derivable1_refl _
  · simpa only [Int.zero_mul,Int.add_zero,Int.sub_zero] using intArray.undef_seg_merge_to_undef_full a 0 len total hc

theorem proof_of_energyNecklace_entail_wit_1 : energyNecklace_entail_wit_1 := by
  right
  intro n_pre beads_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hz : Forall2 Eq (sublist 0 0 ([] : List Int)) (sublist 0 0 beads_l) := by simp only [Zsublist_of_nil,Zsublist_nil beads_l 0 0 (by omega)]; exact .nil
  split_pure_spatial
  · sep_apply (intArray.undef_full_split_to_undef_seg (&("vals")) (2*n_pre) 200 (by omega))
    sep_apply (intArray.undef_full_split_to_undef_seg (&("dp")) ((2*n_pre)*(2*n_pre)) 40000 (by constructor <;> nlinarith))
    sep_apply (intArray.undef_seg_to_undef_full (&("dp")) 0 ((2*n_pre)*(2*n_pre)))
    simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | exact Forall.nil | (simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_2 : energyNecklace_entail_wit_2 := by
  right
  intro n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hlen : Zlength (vals_l_2++[Znth i beads_l 0]) = i+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  have hp : Forall2 Eq (sublist 0 (i+1) (vals_l_2++[Znth i beads_l 0])) (sublist 0 (i+1) beads_l) := by
    apply prefix_view_make _ _ (i+1) (by omega) (by omega) (by omega)
    intro k hk
    by_cases he : k=i
    · subst k
      rw [app_Znth2 0 vals_l_2 [Znth i beads_l 0] i (by omega),PreH9,Int.sub_self,Znth0_cons]
    · rw [app_nth vals_l_2 (Znth i beads_l 0) k (by omega)]
      simpa only [Int.zero_add] using view_get vals_l_2 beads_l 0 i k (by omega) (by omega) (by simpa only [Int.zero_add] using PreH12)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | exact Forall.nil | (simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_3 : energyNecklace_entail_wit_3 := by
  right
  intro n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have he : i=n_pre := by omega
  have hz : Forall2 Eq (sublist n_pre (n_pre+0) vals_l_2) (sublist 0 0 beads_l) := by simp only [Int.add_zero,Zsublist_nil vals_l_2 n_pre n_pre (by omega),Zsublist_nil beads_l 0 0 (by omega)]; exact .nil
  have hp := PreH12
  rw [he] at hp
  Exists vals_l_2
  split_pure_spatial
  · rw [he]; simp only [Int.add_zero]; cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | exact Forall.nil | (simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_4 : energyNecklace_entail_wit_4 := by
  right
  intro n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hlen : Zlength (vals_l_2++[Znth i beads_l 0]) = n_pre+(i+1) := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  have hp : Forall2 Eq (sublist 0 n_pre (vals_l_2++[Znth i beads_l 0])) (sublist 0 n_pre beads_l) := by
    apply prefix_view_make _ _ n_pre (by omega) (by omega) (by omega)
    intro k hk
    rw [app_nth vals_l_2 (Znth i beads_l 0) k (by omega)]
    simpa only [Int.zero_add] using view_get vals_l_2 beads_l 0 n_pre k (by omega) hk (by simpa only [Int.zero_add] using PreH12)
  have hq : Forall2 Eq (sublist n_pre (n_pre+(i+1)) (vals_l_2++[Znth i beads_l 0])) (sublist 0 (i+1) beads_l) := by
    apply view_make _ _ n_pre (i+1) (by omega) (by omega) (by omega) (by omega)
    intro k hk
    by_cases he : k=i
    · subst k
      rw [app_Znth2 0 vals_l_2 [Znth i beads_l 0] (n_pre+i) (by omega),PreH9,Int.sub_self,Znth0_cons]
    · rw [app_nth vals_l_2 (Znth i beads_l 0) (n_pre+k) (by omega)]
      exact view_get vals_l_2 beads_l n_pre i k (by omega) (by omega) PreH13
  Exists (vals_l_2++[Znth i beads_l 0])
  split_pure_spatial
  · have he : n_pre+i+1=n_pre+(i+1) := by omega
    rw [he]; cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | exact Forall.nil | (simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_5 : energyNecklace_entail_wit_5 := by
  right
  intro n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have he : i=n_pre := by omega
  have hd : EnergyValsDuplicated beads_l vals_l_2 n_pre := by
    refine ⟨by omega,by assumption,by omega,?_,?_⟩
    · intro k hk
      simpa only [Int.zero_add] using view_get vals_l_2 beads_l 0 n_pre k (by omega) hk (by simpa only [Int.zero_add] using PreH12)
    · intro k hk
      exact view_get vals_l_2 beads_l n_pre n_pre k (by omega) hk (by simpa only [he] using PreH13)
  Exists vals_l_2
  split_pure_spatial
  · have heq : n_pre+i=total := by omega
    rw [heq]
    simpa only [Int.zero_mul,Int.add_zero,Int.sub_zero] using intArray.seg_to_full (&("vals")) 0 total vals_l_2
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | exact Forall.nil | (simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_6 : energyNecklace_entail_wit_6 := by
  right
  intro n_pre beads_l vals_l_2 i dp_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hz : Forall (Eq (0 : Int)) (dp_l_2++[0]) := by
    apply Forall.iff_forall_mem.mpr
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact PreH12.mem hx
    · have he : x=0 := by simpa using hx
      exact he.symm
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | exact Forall.nil | (simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_7 : energyNecklace_entail_wit_7 := by
  right
  intro n_pre beads_l vals_l_2 i dp_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have he : i=total*width := by omega
  have hz : EnergyZeroTable dp_l_2 total width := ⟨by omega,by assumption,by omega,fun k hk => (nth_property _ dp_l_2 k PreH12 (by omega)).symm⟩
  have hd := EnergyZeroTable_len_done_2__prefix_table_bootstrap vals_l_2 dp_l_2 total width (by have h := PreH13.2.2.1; omega) hz
  have hp : EnergyLengthsComplete vals_l_2 dp_l_2 width 2 := hd.2.2.2.2.2
  have hvals := PreH13.2.2.1
  Exists dp_l_2
  split_pure_spatial
  · rw [he]
    simpa only [Int.zero_mul,Int.add_zero,Int.sub_zero] using intArray.seg_to_full (&("dp")) 0 (total*width) dp_l_2
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | exact Forall.nil | (simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega) | nlinarith

theorem proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22 := by
  right
  intro n_pre beads_l vals_l dp_l answer start_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hp : EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start_2 answer := ⟨PreH14,PreH13,PreH3,⟨PreH8,PreH9⟩,⟨PreH10,PreH11⟩,PreH28⟩
  have ha := EnergyAnswerProgress_finish__answer_loop beads_l vals_l dp_l n_pre total width start_2 answer PreH4 hp PreH1 PreH9
  split_pure_spatial
  · have he : total*width=(2*n_pre)*(2*n_pre) := by rw [PreH3,PreH2]
    rw [he]
    have ht : total=2*n_pre := PreH2
    rw [ht]
    sep_apply (scratch_cleanup (&("vals")) (2*n_pre) 200 vals_l (by omega))
    sep_apply (scratch_cleanup (&("dp")) ((2*n_pre)*(2*n_pre)) 40000 dp_l (by constructor <;> nlinarith))
    cancel
  · dump_pre_spatial
    exact ha

end SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_proof_manual
