import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib
open AUXLib

inductive ReachableAmount (coins : List Int) : Int → Prop where
  | ReachableAmount_zero : ReachableAmount coins 0
  | ReachableAmount_add (v c : Int) : ReachableAmount coins v → c ∈ coins → 0 < c →
      ReachableAmount coins (v + c)
export ReachableAmount (ReachableAmount_zero ReachableAmount_add)

def MaxReachableAmount (coins : List Int) (amount ans : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·)
    (fun v => ReachableAmount coins v ∧ 0 ≤ v ∧ v ≤ amount) (fun v => v) ans

def DpPrefixZeroed (dp : List Int) (hi : Int) : Prop :=
  0 ≤ hi ∧ Zlength dp ≥ hi ∧ Znth 0 dp 0 = 1 ∧
    ∀ k : Int, (1 ≤ k ∧ k < hi) → Znth k dp 0 = 0

def DpReachableTable (coins dp : List Int) (hi : Int) : Prop :=
  0 ≤ hi ∧ Zlength dp ≥ hi ∧
    ∀ k : Int, (0 ≤ k ∧ k < hi) → (Znth k dp 0 ≠ 0 ↔ ReachableAmount coins k)

def DpCoinInnerProgress (prev_coins : List Int) (coin : Int) (dp : List Int)
    (j amount : Int) : Prop :=
  0 < coin ∧ coin ≤ j ∧ j ≤ amount + 1 ∧ Zlength dp ≥ amount + 1 ∧
  (∀ k : Int, (0 ≤ k ∧ k < j) →
    (Znth k dp 0 ≠ 0 ↔ ReachableAmount (prev_coins ++ [coin]) k)) ∧
  ∀ k : Int, (j ≤ k ∧ k < amount + 1) →
    (Znth k dp 0 ≠ 0 ↔ ReachableAmount prev_coins k)

def NoReachableAbove (coins : List Int) (amount res : Int) : Prop :=
  (0 ≤ res ∧ res ≤ amount) ∧ ∀ k : Int, (res < k ∧ k ≤ amount) → ¬ ReachableAmount coins k


theorem MaxReachableAmount_intro_no_above (coins : List Int) (amount res : Int)
    (hr : ReachableAmount coins res) (h0 : 0 ≤ res) (ha : res ≤ amount)
    (hn : NoReachableAbove coins amount res) : MaxReachableAmount coins amount res := by
  refine ⟨res, ⟨⟨hr, h0, ha⟩, ?_⟩, rfl⟩
  intro b hb
  change b ≤ res
  by_contra h
  exact hn.2 b ⟨by omega, hb.2.2⟩ hb.1

theorem ReachableAmount_nil_inv (v : Int) (h : ReachableAmount [] v) : v = 0 := by
  generalize he : ([] : List Int) = coins at h
  induction h with
  | ReachableAmount_zero => rfl
  | ReachableAmount_add v c h hc hp ih => simp [← he] at hc

theorem DpPrefixZeroed_snoc_zero (dp : List Int) (j : Int) (hj : 0 < j)
    (hp : DpPrefixZeroed dp j) (hlen : Zlength (dp ++ [0]) = j + 1) :
    DpPrefixZeroed (dp ++ [0]) (j + 1) := by
  have hd : Zlength dp = j := by simp only [Zlength_app, Zlength_cons, Zlength_nil] at hlen; omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have he : Znth 0 (dp ++ [0]) 0 = Znth 0 dp 0 :=
      ListLib.app_Znth1 0 dp [0] 0 (by change 0 ≤ 0 ∧ 0 < Zlength dp; omega)
    rw [he]; exact hp.2.2.1
  · intro k hk
    by_cases hkj : k < j
    · have he : Znth k (dp ++ [0]) 0 = Znth k dp 0 :=
        ListLib.app_Znth1 0 dp [0] k (by change 0 ≤ k ∧ k < Zlength dp; omega)
      rw [he]; exact hp.2.2.2 k ⟨hk.1, hkj⟩
    · have he : k = j := by omega
      rw [he, app_Znth2 0 dp [0] j (by omega), hd, Int.sub_self]
      rfl

theorem DpPrefixZeroed_to_DpReachableTable_nil (dp : List Int) (hi : Int)
    (hp : DpPrefixZeroed dp hi) : DpReachableTable [] dp hi := by
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro k hk
  constructor
  · intro hz
    by_cases h : k = 0
    · subst k; exact ReachableAmount_zero
    · exact False.elim (hz (hp.2.2.2 k (by omega)))
  · intro hr
    have he := ReachableAmount_nil_inv k hr
    subst k
    rw [hp.2.2.1]
    omega

theorem ReachableAmount_nonneg (coins : List Int) (v : Int) (h : ReachableAmount coins v) : 0 ≤ v := by
  induction h with
  | ReachableAmount_zero => omega
  | ReachableAmount_add v c h hc hp ih => omega

theorem ReachableAmount_mono_incl (coins1 coins2 : List Int) (v : Int)
    (hi : ∀ c, c ∈ coins1 → c ∈ coins2) (h : ReachableAmount coins1 v) :
    ReachableAmount coins2 v := by
  induction h with
  | ReachableAmount_zero => exact ReachableAmount_zero
  | ReachableAmount_add v c h hc hp ih => exact ReachableAmount_add v c ih (hi c hc) hp

theorem ReachableAmount_app_single_below (coins : List Int) (coin k : Int)
    (hc : 0 < coin) (hk : 0 ≤ k ∧ k < coin) :
    ReachableAmount (coins ++ [coin]) k ↔ ReachableAmount coins k := by
  constructor
  · intro h
    induction h with
    | ReachableAmount_zero => exact ReachableAmount_zero
    | ReachableAmount_add v c h hin hp ih =>
      rcases List.mem_append.mp hin with hin | hin
      · exact ReachableAmount_add v c (ih ⟨ReachableAmount_nonneg _ _ h, by omega⟩) hin hp
      · simp only [List.mem_singleton] at hin
        have := ReachableAmount_nonneg _ _ h
        omega
  · exact ReachableAmount_mono_incl coins (coins ++ [coin]) k (fun c h => List.mem_append_left _ h)

theorem DpCoinInnerProgress_replace_current (prev : List Int) (coin : Int) (dp : List Int)
    (j amount : Int) (hm : Znth (j - coin) dp 0 ≠ 0) (hja : j ≤ amount)
    (hp : DpCoinInnerProgress prev coin dp j amount) :
    DpCoinInnerProgress prev coin (replace_Znth j 1 dp) (j + 1) amount := by
  rcases hp with ⟨hc, hcj, hja1, hlen, hb, ha⟩
  have hj : 0 ≤ j ∧ j < Zlength dp := by omega
  refine ⟨hc, by omega, by omega, ?_, ?_, ?_⟩
  · rw [Zlength_replace_Znth]; exact hlen
  · intro k hk
    by_cases he : k = j
    · subst k
      rw [Znth_replace_Znth_Same 0 dp j 1 hj]
      have hr := (hb (j - coin) (by omega)).mp hm
      have hadd : ReachableAmount (prev ++ [coin]) j := by
        convert ReachableAmount_add (j - coin) coin hr (by simp) hc using 1 <;> omega
      exact ⟨fun _ => hadd, fun _ => by omega⟩
    · rw [Znth_replace_Znth_Diff 0 dp j k 1 hj (by omega) (Ne.symm he)]
      exact hb k (by omega)
  · intro k hk
    rw [Znth_replace_Znth_Diff 0 dp j k 1 hj (by omega) (by omega)]
    exact ha k (by omega)

theorem ReachableAmount_app_l (coins extra : List Int) (v : Int)
    (h : ReachableAmount coins v) : ReachableAmount (coins ++ extra) v :=
  ReachableAmount_mono_incl coins (coins ++ extra) v (fun _ h => List.mem_append_left _ h) h

theorem ReachableAmount_app_single_inv (prev : List Int) (coin v : Int) (hc : 0 < coin)
    (h : ReachableAmount (prev ++ [coin]) v) :
    ReachableAmount prev v ∨ (coin ≤ v ∧ ReachableAmount (prev ++ [coin]) (v - coin)) := by
  induction h with
  | ReachableAmount_zero => exact Or.inl ReachableAmount_zero
  | ReachableAmount_add v c h hin hp ih =>
    rcases List.mem_append.mp hin with hinp | hins
    · rcases ih with hv | ⟨hle, hm⟩
      · exact Or.inl (ReachableAmount_add v c hv hinp hp)
      · refine Or.inr ⟨by omega, ?_⟩
        convert ReachableAmount_add (v - coin) c hm hin hp using 1 <;> omega
    · simp only [List.mem_singleton] at hins
      subst c
      have hn := ReachableAmount_nonneg _ _ h
      exact Or.inr ⟨by omega, by simpa using h⟩

theorem ReachableAmount_app_single_lt (prev : List Int) (coin v : Int)
    (hc : 0 < coin) (hv : v < coin) (hr : ReachableAmount (prev ++ [coin]) v) :
    ReachableAmount prev v := by
  rcases ReachableAmount_app_single_inv prev coin v hc hr with h | ⟨h, _⟩
  · exact h
  · omega

theorem sublist_0_succ_app {A : Type} (d : A) (l : List A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l d] := by
  rw [sublist_split 0 (i + 1) i l (by omega) (by omega), sublist_single d i l hi]

end SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib
