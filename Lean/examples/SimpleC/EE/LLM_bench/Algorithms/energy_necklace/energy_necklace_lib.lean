import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib
open AUXLib

def EnergyValsDuplicated (beads vals : List Int) (n : Int) : Prop :=
  0 ≤ n ∧ Zlength beads = n ∧ Zlength vals = 2 * n ∧
  (∀ i : Int, (0 ≤ i ∧ i < n) → Znth i vals 0 = Znth i beads 0) ∧
  (∀ i : Int, (0 ≤ i ∧ i < n) → Znth (n + i) vals 0 = Znth i beads 0)

def EnergyLabelsBounded (beads : List Int) (n : Int) : Prop :=
  Zlength beads = n ∧ ∀ i : Int, (0 ≤ i ∧ i < n) → (1 ≤ Znth i beads 0 ∧ Znth i beads 0 ≤ 1000)

inductive EnergyIntervalPlan (vals : List Int) : Int → Int → Int → Prop where
  | EnergyIntervalPlan_single (left : Int) : 0 ≤ left → left + 1 < Zlength vals →
      EnergyIntervalPlan vals left left 0
  | EnergyIntervalPlan_merge (left split right e_left e_right : Int) :
      0 ≤ left → (left ≤ split ∧ split < right) → right + 1 < Zlength vals →
      EnergyIntervalPlan vals left split e_left → EnergyIntervalPlan vals (split + 1) right e_right →
      EnergyIntervalPlan vals left right
        (e_left + e_right + Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0)
export EnergyIntervalPlan (EnergyIntervalPlan_single EnergyIntervalPlan_merge)

def EnergyIntervalBest (vals : List Int) (left right answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun energy => EnergyIntervalPlan vals left right energy)
    (fun energy => energy) answer

def EnergyRotationBest (beads : List Int) (n start answer : Int) : Prop :=
  ∃ vals, EnergyValsDuplicated beads vals n ∧ (0 ≤ start ∧ start < n) ∧
    EnergyIntervalBest vals start (start + n - 1) answer

def EnergyNecklaceAnswer (beads : List Int) (n answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·)
    (fun energy => ∃ start : Int, (0 ≤ start ∧ start < n) ∧ EnergyRotationBest beads n start energy)
    (fun energy => energy) answer

def EnergyCellIndex (width left right : Int) : Int := left * width + right

def EnergyZeroTable (dp : List Int) (total width : Int) : Prop :=
  0 ≤ total ∧ width = total ∧ Zlength dp = total * width ∧
  ∀ idx : Int, (0 ≤ idx ∧ idx < total * width) → Znth idx dp 0 = 0

def EnergyLenDone (vals dp : List Int) (total width len : Int) : Prop :=
  0 ≤ total ∧ width = total ∧ Zlength vals = total ∧ Zlength dp = total * width ∧ 1 ≤ len ∧
  ∀ l left right idx : Int, (1 ≤ l ∧ l < len) → right = left + l - 1 →
    idx = EnergyCellIndex width left right → 0 ≤ left → left + l < Zlength vals →
    EnergyIntervalBest vals left right (Znth idx dp 0)

def EnergyLeftProgress (vals dp : List Int) (total width len left : Int) : Prop :=
  EnergyLenDone vals dp total width len ∧ 2 ≤ len ∧ 0 ≤ left ∧
  ∀ done_left right idx : Int, (0 ≤ done_left ∧ done_left < left) → right = done_left + len - 1 →
    idx = EnergyCellIndex width done_left right → done_left + len < Zlength vals →
    EnergyIntervalBest vals done_left right (Znth idx dp 0)

def EnergySplitCandidate (vals dp : List Int) (width left right split candidate : Int) : Prop :=
  (left ≤ split ∧ split < right) ∧ right + 1 < Zlength vals ∧
  candidate = Znth (EnergyCellIndex width left split) dp 0 +
    Znth (EnergyCellIndex width (split + 1) right) dp 0 +
    Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0

def EnergySplitProgress (vals dp : List Int) (total width len left split best : Int) : Prop :=
  EnergyLeftProgress vals dp total width len left ∧
  let right := left + len - 1
  2 ≤ len ∧ 0 ≤ left ∧ left + len ≤ total ∧ right = left + len - 1 ∧
  (left ≤ split ∧ split ≤ right) ∧ (0 ≤ best ∧ best ≤ 2100000000) ∧
  ((split = left ∧ best = 0) ∨ (left < split ∧
    MaxMinLib.max_value_of_subset (· ≤ ·)
      (fun candidate => ∃ k : Int, (left ≤ k ∧ k < split) ∧
        EnergySplitCandidate vals dp width left right k candidate)
      (fun candidate => candidate) best))

def EnergyUpdatedCell (vals old_dp new_dp : List Int) (width left right value : Int) : Prop :=
  (0 ≤ EnergyCellIndex width left right ∧ EnergyCellIndex width left right < Zlength old_dp) ∧
  new_dp = replace_Znth (EnergyCellIndex width left right) value old_dp ∧ EnergyIntervalBest vals left right value

def EnergyAnswerProgress (beads vals dp : List Int) (n total width start answer : Int) : Prop :=
  EnergyValsDuplicated beads vals n ∧ Zlength dp = total * width ∧ width = total ∧
  (0 ≤ start ∧ start ≤ n) ∧ (0 ≤ answer ∧ answer ≤ 2100000000) ∧
  ((start = 0 ∧ answer = 0) ∨ (0 < start ∧
    MaxMinLib.max_value_of_subset (· ≤ ·)
      (fun value => ∃ s : Int, (0 ≤ s ∧ s < start) ∧ EnergyIntervalBest vals s (s + n - 1) value)
      (fun value => value) answer))

def EnergySplitArithmeticBounded (vals dp : List Int) (width left right split bound : Int) : Prop :=
  let left_value := Znth (EnergyCellIndex width left split) dp 0
  let right_value := Znth (EnergyCellIndex width (split + 1) right) dp 0
  let gain := Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0
  (0 ≤ left_value ∧ left_value ≤ bound) ∧ (0 ≤ right_value ∧ right_value ≤ bound) ∧
  (0 ≤ gain ∧ gain ≤ bound) ∧ (0 ≤ left_value + right_value ∧ left_value + right_value ≤ bound) ∧
  (0 ≤ left_value + right_value + gain ∧ left_value + right_value + gain ≤ bound)

def EnergyComputationBounded (beads : List Int) (n bound : Int) : Prop :=
  0 ≤ bound ∧
  (∀ vals dp total width len left right split,
    EnergyValsDuplicated beads vals n → total = 2 * n → width = total → (2 ≤ len ∧ len ≤ n) →
    (0 ≤ left ∧ left < total - len) → right = left + len - 1 → (left ≤ split ∧ split < right) →
    Zlength dp = total * width → EnergyLenDone vals dp total width len →
    EnergySplitArithmeticBounded vals dp width left right split bound) ∧
  (∀ vals left right answer, EnergyValsDuplicated beads vals n → 0 ≤ left → left ≤ right →
    right + 1 < Zlength vals → EnergyIntervalBest vals left right answer → (0 ≤ answer ∧ answer ≤ bound)) ∧
  (∀ vals dp total width start, EnergyValsDuplicated beads vals n → total = 2 * n → width = total →
    (0 ≤ start ∧ start < n) → Zlength dp = total * width → EnergyLenDone vals dp total width (n + 1) →
    (0 ≤ Znth (EnergyCellIndex width start (start + n - 1)) dp 0 ∧
     Znth (EnergyCellIndex width start (start + n - 1)) dp 0 ≤ bound))

set_option maxHeartbeats 4000000

private theorem maximum_iff (P : Int → Prop) (v : Int) :
    MaxMinLib.max_value_of_subset (· ≤ ·) P id v ↔ P v ∧ ∀ x, P x → x ≤ v := by
  constructor
  · rintro ⟨x, ⟨hx, hl⟩, rfl⟩; exact ⟨hx, hl⟩
  · rintro ⟨hx, hl⟩; exact ⟨v, ⟨hx, hl⟩, rfl⟩

private theorem max_scan_step (P : Int → Int → Prop) (lo cut best candidate : Int)
    (hlo : lo ≤ cut) (hc : P cut candidate) (hcn : 0 ≤ candidate)
    (huniq : ∀ k a b, P k a → P k b → a = b)
    (hscan : (cut = lo ∧ best = 0) ∨ (lo < cut ∧
      MaxMinLib.max_value_of_subset (· ≤ ·) (fun v => ∃ k, (lo ≤ k ∧ k < cut) ∧ P k v) id best)) :
    MaxMinLib.max_value_of_subset (· ≤ ·)
      (fun v => ∃ k, (lo ≤ k ∧ k < cut+1) ∧ P k v) id (max best candidate) := by
  apply (maximum_iff _ _).mpr
  constructor
  · rcases hscan with ⟨he, hb⟩ | ⟨hlt, hm⟩
    · rw [hb, max_eq_right hcn]
      exact ⟨cut, ⟨hlo, by omega⟩, hc⟩
    · by_cases hb : best ≤ candidate
      · rw [max_eq_right hb]; exact ⟨cut, ⟨hlo, by omega⟩, hc⟩
      · rw [max_eq_left (by omega : candidate ≤ best)]
        obtain ⟨k, hk, hp⟩ := ((maximum_iff _ best).mp hm).1
        exact ⟨k, ⟨hk.1, by omega⟩, hp⟩
  · rintro v ⟨k, hk, hp⟩
    by_cases hlt : k < cut
    · have hs := hscan.resolve_left (by intro h; omega)
      exact le_trans (((maximum_iff _ best).mp hs.2).2 v ⟨k, ⟨hk.1, hlt⟩, hp⟩) (le_max_left _ _)
    · have he : k = cut := by omega
      subst k
      rw [huniq cut v candidate hp hc]
      exact le_max_right _ _

private theorem index_bounds (width l r : Int) (hw : 0 < width)
    (hl : 0 ≤ l ∧ l < width) (hr : 0 ≤ r ∧ r < width) :
    0 ≤ EnergyCellIndex width l r ∧ EnergyCellIndex width l r < width*width := by
  unfold EnergyCellIndex
  constructor
  · exact add_nonneg (mul_nonneg hl.1 (by omega)) hr.1
  · nlinarith

theorem EnergyValsDuplicated_label_bound__arithmetic_safety_bounds (beads vals : List Int) (n i : Int)
    (hd : EnergyValsDuplicated beads vals n) (hb : EnergyLabelsBounded beads n) (hi : 0 ≤ i ∧ i < 2*n) :
    1 ≤ Znth i vals 0 ∧ Znth i vals 0 ≤ 1000 := by
  by_cases hl : i < n
  · rw [hd.2.2.2.1 i ⟨hi.1, hl⟩]; exact hb.2 i ⟨hi.1, hl⟩
  · have he : i = n+(i-n) := by omega
    rw [he, hd.2.2.2.2 (i-n) ⟨by omega, by omega⟩]
    exact hb.2 (i-n) ⟨by omega, by omega⟩

theorem EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
    (beads vals dp : List Int) (n total width len left right split best bound : Int)
    (hb : EnergyComputationBounded beads n bound) (hd : EnergyValsDuplicated beads vals n)
    (ht : total = 2*n) (hw : width = total) (hl : 2 ≤ len ∧ len ≤ n)
    (hlf : 0 ≤ left ∧ left < total-len) (hr : right = left+len-1)
    (hk : left ≤ split ∧ split < right) (hsize : Zlength dp = total*width)
    (hp : EnergySplitProgress vals dp total width len left split best) :
    EnergySplitArithmeticBounded vals dp width left right split bound :=
  hb.2.1 vals dp total width len left right split hd ht hw hl hlf hr hk hsize hp.1.1

theorem EnergyIntervalBest_single_zero__prefix_table_bootstrap (vals : List Int) (left : Int)
    (hl : 0 ≤ left) (hr : left+1 < Zlength vals) : EnergyIntervalBest vals left left 0 := by
  apply (maximum_iff _ _).mpr
  refine ⟨EnergyIntervalPlan_single left hl hr, ?_⟩
  intro cost hp
  cases hp with
  | EnergyIntervalPlan_single => omega
  | EnergyIntervalPlan_merge l k r lc rc hl hb => omega

theorem EnergyZeroTable_len_done_2__prefix_table_bootstrap (vals dp : List Int) (total width : Int)
    (hv : Zlength vals = total) (hz : EnergyZeroTable dp total width) :
    EnergyLenDone vals dp total width 2 := by
  refine ⟨hz.1, hz.2.1, hv, hz.2.2.1, by omega, ?_⟩
  intro l left right idx hl hr hi hleft hfit
  have he : l = 1 := by omega
  have her : right = left := by omega
  subst l
  rw [her, hi, her]
  have hb := index_bounds width left left (by have := hz.2.1; omega)
    ⟨hleft, by have := hz.2.1; omega⟩ ⟨hleft, by have := hz.2.1; omega⟩
  rw [hz.2.2.2 _ (by rw [←hz.2.1]; exact hb)]
  exact EnergyIntervalBest_single_zero__prefix_table_bootstrap vals left hleft hfit

theorem EnergyZeroTable_from_prefix__prefix_table_bootstrap (dp : List Int) (total width i : Int)
    (ht : 0 ≤ total) (hw : width = total) (hge : i ≥ total*width) (hle : i ≤ total*width)
    (hlen : Zlength dp = i) (hz : ∀ k, (0 ≤ k ∧ k < i) → Znth k dp 0 = 0) :
    EnergyZeroTable dp total width := ⟨ht, hw, by omega, fun k hk => hz k ⟨hk.1, by omega⟩⟩

theorem EnergySplitCandidate_ext_eq__dp_interval_progress (vals dp : List Int)
    (width left right split a b : Int) (ha : EnergySplitCandidate vals dp width left right split a)
    (hb : EnergySplitCandidate vals dp width left right split b) : a = b := ha.2.2.trans hb.2.2.symm

theorem EnergySplitProgress_step_keep__dp_interval_progress (vals dp : List Int)
    (total width len left right split best candidate : Int) (hr : right = left+len-1)
    (hk : left ≤ split ∧ split < right) (hp : EnergySplitProgress vals dp total width len left split best)
    (hc : EnergySplitCandidate vals dp width left right split candidate) (hc0 : 0 ≤ candidate) (hb : candidate ≤ best) :
    EnergySplitProgress vals dp total width len left (split+1) best := by
  rcases hp with ⟨hlp, hlen, hleft, hfit, hre, hsplit, hbest, hscan⟩
  refine ⟨hlp, hlen, hleft, hfit, rfl, ⟨by omega, by omega⟩, hbest, Or.inr ⟨by omega, ?_⟩⟩
  rw [hr] at hc
  simpa only [max_eq_left hb] using max_scan_step (EnergySplitCandidate vals dp width left (left+len-1))
    left split best candidate hk.1 hc hc0 (EnergySplitCandidate_ext_eq__dp_interval_progress vals dp width left (left+len-1)) hscan

theorem EnergySplitProgress_step_take__dp_interval_progress (vals dp : List Int)
    (total width len left right split best candidate : Int) (hr : right = left+len-1)
    (hk : left ≤ split ∧ split < right) (hp : EnergySplitProgress vals dp total width len left split best)
    (hc : EnergySplitCandidate vals dp width left right split candidate) (hcb : 0 ≤ candidate ∧ candidate ≤ 2100000000)
    (hb : best < candidate) : EnergySplitProgress vals dp total width len left (split+1) candidate := by
  rcases hp with ⟨hlp, hlen, hleft, hfit, hre, hsplit, hbest, hscan⟩
  refine ⟨hlp, hlen, hleft, hfit, rfl, ⟨by omega, by omega⟩, hcb, Or.inr ⟨by omega, ?_⟩⟩
  rw [hr] at hc
  simpa only [max_eq_right (le_of_lt hb)] using max_scan_step (EnergySplitCandidate vals dp width left (left+len-1))
    left split best candidate hk.1 hc hcb.1 (EnergySplitCandidate_ext_eq__dp_interval_progress vals dp width left (left+len-1)) hscan

private theorem child_best (vals dp : List Int) (total width len left right k : Int)
    (hd : EnergyLenDone vals dp total width len) (hr : right = left+len-1) (hl : 0 ≤ left)
    (hk : left ≤ k ∧ k < right) (hrb : right+1 < Zlength vals) :
    EnergyIntervalBest vals left k (Znth (EnergyCellIndex width left k) dp 0) ∧
    EnergyIntervalBest vals (k+1) right (Znth (EnergyCellIndex width (k+1) right) dp 0) :=
  ⟨hd.2.2.2.2.2 (k-left+1) left k _ ⟨by omega, by omega⟩ (by omega) rfl hl (by omega),
   hd.2.2.2.2.2 (right-k) (k+1) right _ ⟨by omega, by omega⟩ (by omega) rfl (by omega) (by omega)⟩

theorem EnergySplitCandidate_plan__dp_interval_progress (vals dp : List Int)
    (total width len left right split candidate : Int) (hd : EnergyLenDone vals dp total width len)
    (hr : right = left+len-1) (hl : 0 ≤ left) (hk : left ≤ split ∧ split < right)
    (hrb : right+1 < Zlength vals) (hc : EnergySplitCandidate vals dp width left right split candidate) :
    EnergyIntervalPlan vals left right candidate := by
  have hb := child_best vals dp total width len left right split hd hr hl hk hrb
  rw [hc.2.2]
  exact EnergyIntervalPlan_merge left split right _ _ hl hk hrb
    ((maximum_iff _ _).mp hb.1).1 ((maximum_iff _ _).mp hb.2).1

theorem EnergySplitProgress_finish_interval_best__dp_interval_progress (vals dp : List Int)
    (total width len left right split best : Int) (hr : right = left+len-1) (hs : split ≥ right)
    (hrb : right+1 < Zlength vals) (hp : EnergySplitProgress vals dp total width len left split best) :
    EnergyIntervalBest vals left right best := by
  rcases hp with ⟨hlp, hlen, hleft, hfit, hre, hsplit, hbest, hscan⟩
  have he : split = right := by omega
  subst split
  have hm := hscan.resolve_left (by intro h; omega)
  rw [←hr] at hm
  have hm' := (maximum_iff _ best).mp hm.2
  apply (maximum_iff _ best).mpr
  constructor
  · obtain ⟨k, hk, hc⟩ := hm'.1
    exact EnergySplitCandidate_plan__dp_interval_progress vals dp total width len left right k best hlp.1 hr hleft hk hrb hc
  · intro cost hplan
    cases hplan with
    | EnergyIntervalPlan_single => omega
    | EnergyIntervalPlan_merge l k r lc rc hl hk hd hpl hpr =>
      have hch := child_best vals dp total width len left right k hlp.1 hr hleft hk hrb
      have hbl := ((maximum_iff _ _).mp hch.1).2 lc hpl
      have hbr := ((maximum_iff _ _).mp hch.2).2 rc hpr
      have hcan := hm'.2 _ ⟨k, hk, hk, hd, rfl⟩
      omega

theorem EnergyCellIndex_inj__dp_interval_progress (width l r l' r' : Int)
    (hw : 0 < width) (hr : 0 ≤ r ∧ r < width) (hr' : 0 ≤ r' ∧ r' < width)
    (he : EnergyCellIndex width l r = EnergyCellIndex width l' r') : l = l' ∧ r = r' := by
  unfold EnergyCellIndex at he
  have hl : l = l' := by
    rcases lt_trichotomy l l' with h | h | h
    · have hp := mul_le_mul_of_nonneg_right (show l+1 ≤ l' by omega) (show 0 ≤ width by omega); nlinarith
    · exact h
    · have hp := mul_le_mul_of_nonneg_right (show l'+1 ≤ l by omega) (show 0 ≤ width by omega); nlinarith
  exact ⟨hl, by rw [hl] at he; omega⟩

theorem EnergyLenDone_replace_current__dp_interval_progress (vals dp : List Int)
    (total width len left right best : Int) (hr : right = left+len-1) (hl : 0 ≤ left)
    (hfit : left < total-len) (hd : EnergyLenDone vals dp total width len) :
    EnergyLenDone vals (replace_Znth (EnergyCellIndex width left right) best dp) total width len := by
  have hw : 0 < width := by have := hd.2.1; have := hd.2.2.2.2.1; omega
  have hrr : 0 ≤ right ∧ right < width := by have := hd.2.1; have := hd.2.2.2.2.1; omega
  have hcur := index_bounds width left right hw ⟨hl, by have := hd.2.1; have := hd.2.2.2.2.1; omega⟩ hrr
  have hsize : Zlength dp = width*width := by rw [hd.2.2.2.1, hd.2.1]
  rw [←hsize] at hcur
  refine ⟨hd.1, hd.2.1, hd.2.2.1, by rw [Zlength_replace_Znth]; exact hd.2.2.2.1, hd.2.2.2.2.1, ?_⟩
  intro l i j idx hb hj hi h0 hf
  have hidx : 0 ≤ idx ∧ idx < Zlength dp := by
    rw [hi, hsize]
    exact index_bounds width i j hw ⟨h0, by have := hd.2.1; have := hd.2.2.1; omega⟩
      ⟨by omega, by have := hd.2.1; have := hd.2.2.1; omega⟩
  have hneq : EnergyCellIndex width left right ≠ idx := by
    intro he
    rw [hi] at he
    have hh := EnergyCellIndex_inj__dp_interval_progress width left right i j hw hrr
      ⟨by omega, by have := hd.2.1; have := hd.2.2.1; omega⟩ he
    omega
  rw [Znth_replace_Znth_Diff 0 dp _ idx best hcur hidx hneq]
  exact hd.2.2.2.2.2 l i j idx hb hj hi h0 hf

theorem EnergyLeftProgress_step_update__dp_interval_progress (vals dp : List Int)
    (total width len left right best : Int) (hr : right = left+len-1) (hl : 0 ≤ left)
    (hfit : left < total-len) (hp : EnergySplitProgress vals dp total width len left right best)
    (hm : EnergyIntervalBest vals left right best) :
    EnergyLeftProgress vals (replace_Znth (EnergyCellIndex width left right) best dp) total width len (left+1) := by
  have hd := hp.1.1
  have hw : 0 < width := by have := hd.2.1; have := hp.2.1; omega
  have hrr : 0 ≤ right ∧ right < width := by have := hd.2.1; have := hp.2.1; omega
  have hcur := index_bounds width left right hw ⟨hl, by have := hd.2.1; have := hp.2.1; omega⟩ hrr
  have hsize : Zlength dp = width*width := by rw [hd.2.2.2.1, hd.2.1]
  rw [←hsize] at hcur
  refine ⟨EnergyLenDone_replace_current__dp_interval_progress _ _ _ _ _ _ _ _ hr hl hfit hd,
    hp.2.1, by omega, ?_⟩
  intro i j idx hi hj hidx hf
  by_cases he : i = left
  · subst i
    have hej : j = right := by omega
    rw [hidx, hej, Znth_replace_Znth_Same 0 dp _ best hcur]
    exact hm
  · have hiold : 0 ≤ i ∧ i < left := ⟨hi.1, by omega⟩
    have hir : 0 ≤ i ∧ i < width := by have := hd.2.1; have := hp.2.1; omega
    have hjr : 0 ≤ j ∧ j < width := by have := hd.2.1; have := hd.2.2.1; have := hp.2.1; omega
    have hb : 0 ≤ idx ∧ idx < Zlength dp := by rw [hidx, hsize]; exact index_bounds width i j hw hir hjr
    have hn : EnergyCellIndex width left right ≠ idx := by
      intro hh
      rw [hidx] at hh
      have hx := EnergyCellIndex_inj__dp_interval_progress width left right i j hw hrr hjr hh
      omega
    rw [Znth_replace_Znth_Diff 0 dp _ idx best hcur hb hn]
    exact hp.1.2.2.2 i j idx hiold hj hidx hf

theorem EnergyLeftProgress_finish_len__dp_interval_progress (vals dp : List Int)
    (total width len left : Int) (hge : left ≥ total-len) (hle : left ≤ total-len)
    (hp : EnergyLeftProgress vals dp total width len left) : EnergyLenDone vals dp total width (len+1) := by
  have hd := hp.1
  refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, by have := hp.2.1; omega, ?_⟩
  intro l i j idx hl hj hi h0 hf
  by_cases hlt : l < len
  · exact hd.2.2.2.2.2 l i j idx ⟨hl.1, hlt⟩ hj hi h0 hf
  · have he : l = len := by omega
    subst l
    exact hp.2.2.2 i j idx ⟨h0, by have := hd.2.2.1; omega⟩ hj hi hf

theorem EnergyAnswerProgress_answer_bounds__answer_loop (beads vals dp : List Int)
    (n total width start answer : Int) (hp : EnergyAnswerProgress beads vals dp n total width start answer) :
    0 ≤ answer ∧ answer ≤ 2100000000 := hp.2.2.2.2.1

theorem EnergyLenDone_to_answer_len__answer_loop (vals dp : List Int) (total width len n : Int)
    (hlo : len > n) (hhi : len ≤ n+1) (hp : EnergyLenDone vals dp total width len) :
    EnergyLenDone vals dp total width (n+1) := by
  convert hp using 1 <;> omega

theorem EnergyLenDone_rotation_cell_best__answer_loop (vals dp : List Int) (total width n start : Int)
    (hn : 4 ≤ n) (ht : total = 2*n) (hw : width = total) (hs : 0 ≤ start ∧ start < n)
    (hp : EnergyLenDone vals dp total width (n+1)) :
    EnergyIntervalBest vals start (start+n-1) (Znth (EnergyCellIndex width start (start+n-1)) dp 0) :=
  hp.2.2.2.2.2 n start (start+n-1) _ ⟨by omega, by omega⟩ rfl rfl hs.1 (by have := hp.2.2.1; omega)

theorem EnergyAnswerCellBounded__answer_loop (beads vals dp : List Int) (n total width start : Int)
    (hb : EnergyComputationBounded beads n 2100000000) (hd : EnergyValsDuplicated beads vals n)
    (ht : total = 2*n) (hw : width = total) (hs : 0 ≤ start ∧ start < n)
    (hz : Zlength dp = total*width) (hp : EnergyLenDone vals dp total width (n+1)) :
    0 ≤ Znth (EnergyCellIndex width start (start+n-1)) dp 0 ∧ Znth (EnergyCellIndex width start (start+n-1)) dp 0 ≤ 2100000000 :=
  hb.2.2.2 vals dp total width start hd ht hw hs hz hp

theorem EnergyIntervalBest_unique__answer_loop (vals : List Int) (left right a b : Int)
    (ha : EnergyIntervalBest vals left right a) (hb : EnergyIntervalBest vals left right b) : a = b := by
  have hma := (maximum_iff _ a).mp ha
  have hmb := (maximum_iff _ b).mp hb
  exact le_antisymm (hmb.2 a hma.1) (hma.2 b hmb.1)

theorem EnergyValsDuplicated_unique__answer_loop (beads vals1 vals2 : List Int) (n : Int)
    (h1 : EnergyValsDuplicated beads vals1 n) (h2 : EnergyValsDuplicated beads vals2 n) : vals1 = vals2 := by
  apply (ListLib.list_eq_ext vals1 vals2 0).mpr
  refine ⟨by change Zlength vals1 = Zlength vals2; have := h1.2.2.1; have := h2.2.2.1; omega, ?_⟩
  intro i hi
  change Znth i vals1 0 = Znth i vals2 0
  have hib : i < 2*n := by change 0 ≤ i ∧ i < Zlength vals1 at hi; rw [h1.2.2.1] at hi; exact hi.2
  by_cases hl : i < n
  · rw [h1.2.2.2.1 i ⟨hi.1, hl⟩, h2.2.2.2.1 i ⟨hi.1, hl⟩]
  · have he : i = n+(i-n) := by omega
    rw [he, h1.2.2.2.2 (i-n) ⟨by omega, by omega⟩, h2.2.2.2.2 (i-n) ⟨by omega, by omega⟩]

theorem EnergyAnswerProgress_step_keep__answer_loop (beads vals dp : List Int)
    (n total width start answer value : Int) (hp : EnergyAnswerProgress beads vals dp n total width start answer)
    (hs : 0 ≤ start ∧ start < n) (hv : EnergyIntervalBest vals start (start+n-1) value)
    (hv0 : 0 ≤ value) (hb : value ≤ answer) : EnergyAnswerProgress beads vals dp n total width (start+1) answer := by
  refine ⟨hp.1, hp.2.1, hp.2.2.1, ⟨by omega, by omega⟩, hp.2.2.2.2.1, Or.inr ⟨by omega, ?_⟩⟩
  simpa only [max_eq_left hb] using max_scan_step (fun k v => EnergyIntervalBest vals k (k+n-1) v)
    0 start answer value hs.1 hv hv0 (fun k a b => EnergyIntervalBest_unique__answer_loop vals k (k+n-1) a b) hp.2.2.2.2.2

theorem EnergyAnswerProgress_step_update__answer_loop (beads vals dp : List Int)
    (n total width start answer value : Int) (hp : EnergyAnswerProgress beads vals dp n total width start answer)
    (hs : 0 ≤ start ∧ start < n) (hv : EnergyIntervalBest vals start (start+n-1) value)
    (hvb : 0 ≤ value ∧ value ≤ 2100000000) (hb : answer < value) :
    EnergyAnswerProgress beads vals dp n total width (start+1) value := by
  refine ⟨hp.1, hp.2.1, hp.2.2.1, ⟨by omega, by omega⟩, hvb, Or.inr ⟨by omega, ?_⟩⟩
  simpa only [max_eq_right (le_of_lt hb)] using max_scan_step (fun k v => EnergyIntervalBest vals k (k+n-1) v)
    0 start answer value hs.1 hv hvb.1 (fun k a b => EnergyIntervalBest_unique__answer_loop vals k (k+n-1) a b) hp.2.2.2.2.2

theorem EnergyAnswerProgress_finish__answer_loop (beads vals dp : List Int)
    (n total width start answer : Int) (hn : 4 ≤ n) (hp : EnergyAnswerProgress beads vals dp n total width start answer)
    (hslo : start ≥ n) (hshi : start ≤ n) : EnergyNecklaceAnswer beads n answer := by
  have he : start = n := by omega
  subst start
  have hm := hp.2.2.2.2.2.resolve_left (by intro h; omega)
  have hb := (maximum_iff _ answer).mp hm.2
  apply (maximum_iff _ answer).mpr
  constructor
  · obtain ⟨s, hs, hbest⟩ := hb.1
    exact ⟨s, hs, vals, hp.1, hs, hbest⟩
  · rintro v ⟨s, hs, vals', hdup, hs', hbest⟩
    have he := EnergyValsDuplicated_unique__answer_loop beads vals' vals n hdup hp.1
    subst vals'
    exact hb.2 v ⟨s, hs, hbest⟩

end SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib
open AUXLib

def EnergyLengthsComplete (vals dp : List Int) (width len : Int) : Prop :=
  ∀ l left right idx : Int, (1 ≤ l ∧ l < len) → right = left + l - 1 →
    idx = EnergyCellIndex width left right → 0 ≤ left → left + l < Zlength vals →
    EnergyIntervalBest vals left right (Znth idx dp 0)
def EnergyLeftComplete (vals dp : List Int) (width len left : Int) : Prop :=
  ∀ done_left right idx : Int, (0 ≤ done_left ∧ done_left < left) →
    right = done_left + len - 1 → idx = EnergyCellIndex width done_left right →
    done_left + len < Zlength vals → EnergyIntervalBest vals done_left right (Znth idx dp 0)
def EnergySplitBest (vals dp : List Int) (width len left split best : Int) : Prop :=
  (split = left ∧ best = 0) ∨ (left < split ∧
    MaxMinLib.max_value_of_subset Int.le
      (fun candidate => ∃ k : Int, (left ≤ k ∧ k < split) ∧
        EnergySplitCandidate vals dp width left (left + len - 1) k candidate)
      (fun candidate => candidate) best)
theorem EnergyLenDone.toAnnotation (h : EnergyLenDone vals dp total width len) :
    EnergyLengthsComplete vals dp width len := h.2.2.2.2.2
theorem EnergyLeftProgress.toAnnotation (h : EnergyLeftProgress vals dp total width len left) :
    EnergyLeftComplete vals dp width len left := h.2.2.2

end SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib
namespace SimpleC.EE.LLM_bench.Algorithms.energy_necklace
export energy_necklace_lib (EnergyLengthsComplete EnergyLeftComplete EnergySplitBest)
end SimpleC.EE.LLM_bench.Algorithms.energy_necklace

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib
open AUXLib

def EnergyAnswerBest (vals : List Int) (n start answer : Int) : Prop :=
  (start = 0 ∧ answer = 0) ∨ (0 < start ∧
    MaxMinLib.max_value_of_subset (LE.le (α := Int))
      (fun value => ∃ s : Int, (0 ≤ s ∧ s < start) ∧
        EnergyIntervalBest vals s (s + n - 1) value) (fun value => value) answer)

end SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib
namespace SimpleC.EE.LLM_bench.Algorithms.energy_necklace
export energy_necklace_lib (EnergyAnswerBest)
end SimpleC.EE.LLM_bench.Algorithms.energy_necklace
