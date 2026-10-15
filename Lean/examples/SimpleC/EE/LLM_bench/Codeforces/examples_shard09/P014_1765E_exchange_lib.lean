import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib
open AUXLib


open MaxMinLib

def ExchangeStep (a b : Int) (s1 s2 : Int × Int) : Prop :=
  let (g,x) := s1
  let (g',x') := s2
  (g ≥ 1 ∧ g' = g - 1 ∧ x' = x + a) ∨ (x ≥ b ∧ g' = g + 1 ∧ x' = x - b)
def ReachesSilver (n a b q : Int) : Prop :=
  ∃ states : List (Int × Int),
    states ≠ [] ∧ Znth 0 states (0,0) = (q,0) ∧
    (∀ i, (0 ≤ i ∧ i < Zlength states - 1) →
      ExchangeStep a b (Znth i states (0,0)) (Znth (i+1) states (0,0))) ∧
    (let (g,x) := Znth (Zlength states-1) states (0,0); g ≥ 0 ∧ x ≥ n)
def Pre (n a b : Int) : Prop := True
def Spec (n a b out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun q => q ≥ 0 ∧ ReachesSilver n a b q) (fun x => x) out


private theorem len_pos {A : Type u} (xs : List A) (h : xs ≠ []) : 0 < Zlength xs := by
  cases xs with
  | nil => contradiction
  | cons x xs => have := Zlength_nonneg xs; rw [Zlength_cons]; omega

theorem exchange_prepend_steps__exchange_minimum (a b : Int) (s1 s2 : Int × Int)
    (states : List (Int × Int)) (hne : states ≠ []) (hh : Znth 0 states (0,0) = s2)
    (hf : ExchangeStep a b s1 s2)
    (hs : ∀ i, (0 ≤ i ∧ i < Zlength states - 1) →
      ExchangeStep a b (Znth i states (0,0)) (Znth (i+1) states (0,0)))
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength (s1 :: states) - 1) :
    ExchangeStep a b (Znth i (s1 :: states) (0,0)) (Znth (i+1) (s1 :: states) (0,0)) := by
  by_cases he : i = 0
  · subst i
    change ExchangeStep a b s1 (Znth 0 states (0,0))
    rwa [hh]
  · rw [Znth_cons (0,0) i s1 states (by omega), Znth_cons (0,0) (i+1) s1 states (by omega)]
    simp only [Int.add_sub_cancel]
    have hx := hs (i-1) (by rw [Zlength_cons] at hi; omega)
    simpa only [Int.sub_add_cancel] using hx

theorem exchange_prepend_last__exchange_minimum (s : Int × Int)
    (states : List (Int × Int)) (hne : states ≠ []) :
    Znth (Zlength (s :: states) - 1) (s :: states) (0,0) =
      Znth (Zlength states - 1) states (0,0) := by
  have hl := len_pos states hne
  rw [Zlength_cons, Znth_cons (0,0) _ s states (by omega)]
  congr 1 <;> omega

theorem exchange_sell_path__exchange_minimum (a b : Int) (k : Nat) (x : Int) :
    ∃ states : List (Int × Int), states ≠ [] ∧ Znth 0 states (0,0) = ((k : Int),x) ∧
      (∀ i, (0 ≤ i ∧ i < Zlength states - 1) →
        ExchangeStep a b (Znth i states (0,0)) (Znth (i+1) states (0,0))) ∧
      Znth (Zlength states - 1) states (0,0) = (0, x + a * (k : Int)) := by
  induction k generalizing x with
  | zero =>
    refine ⟨[(0,x)], ?_, rfl, ?_, ?_⟩
    · intro h; cases h
    · intro i hi
      change 0 ≤ i ∧ i < 0 at hi
      omega
    · change (0,x) = (0,x+a*0)
      simp only [Int.mul_zero, Int.add_zero]
  | succ k ih =>
    rcases ih (x+a) with ⟨states, hn, hh, hs, hl⟩
    refine ⟨(((k : Int)+1,x) : Int × Int) :: states, ?_, rfl, ?_, ?_⟩
    · intro h; cases h
    · apply exchange_prepend_steps__exchange_minimum a b _ _ states hn hh
      · exact Or.inl ⟨by omega, by omega, rfl⟩
      · exact hs
    · rw [exchange_prepend_last__exchange_minimum _ states hn, hl]
      congr 1
      push_cast
      ring

theorem exchange_sell_trace__exchange_minimum (n a b q : Int)
    (ha : 1 ≤ a) (hq : 0 ≤ q) (hn : n ≤ a*q) : ReachesSilver n a b q := by
  rcases exchange_sell_path__exchange_minimum a b q.toNat 0 with ⟨states, hs, hh, ht, hl⟩
  have he : (q.toNat : Int) = q := Int.toNat_of_nonneg hq
  rw [he] at hh hl
  refine ⟨states, hs, hh, ht, ?_⟩
  rw [hl]
  exact ⟨by omega, by omega⟩

theorem exchange_path_potential__exchange_minimum (a b : Int)
    (states : List (Int × Int)) (start final : Int × Int)
    (ha : 0 ≤ a) (hab : a ≤ b) (hne : states ≠ []) (hh : Znth 0 states (0,0) = start)
    (hs : ∀ i, (0 ≤ i ∧ i < Zlength states - 1) →
      ExchangeStep a b (Znth i states (0,0)) (Znth (i+1) states (0,0)))
    (hl : Znth (Zlength states - 1) states (0,0) = final) :
    a * final.1 + final.2 ≤ a * start.1 + start.2 := by
  induction states generalizing start final with
  | nil => contradiction
  | cons s1 rest ih =>
    cases rest with
    | nil =>
      change s1 = start at hh
      change s1 = final at hl
      rw [← hh, ← hl]
    | cons s2 rest =>
      have hn : s2 :: rest ≠ [] := by intro h; cases h
      have hp := Zlength_nonneg rest
      have hf := hs 0 (by simp only [Zlength_cons]; omega)
      change ExchangeStep a b s1 s2 at hf
      have ht : ∀ i, (0 ≤ i ∧ i < Zlength (s2 :: rest) - 1) →
          ExchangeStep a b (Znth i (s2 :: rest) (0,0)) (Znth (i+1) (s2 :: rest) (0,0)) := by
        intro i hi
        have hh' := hs (i+1) (by simp only [Zlength_cons] at *; omega)
        rw [Znth_cons (0,0) (i+1) s1 (s2::rest) (by omega),
          Znth_cons (0,0) (i+1+1) s1 (s2::rest) (by omega)] at hh'
        simpa only [Int.add_sub_cancel] using hh'
      rw [exchange_prepend_last__exchange_minimum s1 (s2::rest) hn] at hl
      have ht' := ih s2 final hn rfl ht hl
      change s1 = start at hh
      rw [← hh]
      rcases s1 with ⟨g1,x1⟩
      rcases s2 with ⟨g2,x2⟩
      rcases hf with ⟨hg, he1, he2⟩ | ⟨hx, he1, he2⟩
      · dsimp at ht' ⊢
        rw [he1, he2] at ht'
        nlinarith
      · dsimp at ht' ⊢
        rw [he1, he2] at ht'
        nlinarith

theorem exchange_nonprofitable_lower_bound__exchange_minimum (n a b q : Int)
    (ha : 0 ≤ a) (hab : a ≤ b) (hr : ReachesSilver n a b q) : n ≤ a*q := by
  rcases hr with ⟨states, hs, hh, ht, hf⟩
  generalize he : Znth (Zlength states - 1) states (0,0) = final at hf
  rcases final with ⟨g,x⟩
  have hp := exchange_path_potential__exchange_minimum a b states (q,0) (g,x) ha hab hs hh ht he
  dsimp at hf hp
  have hm := mul_nonneg ha hf.1
  omega


theorem exchange_cycle_path__exchange_minimum (a b : Int) (k : Nat) (x : Int)
    (hx : b ≤ x) (hab : b ≤ a) :
    ∃ states : List (Int × Int), states ≠ [] ∧ Znth 0 states (0,0) = (0,x) ∧
      (∀ i, (0 ≤ i ∧ i < Zlength states - 1) →
        ExchangeStep a b (Znth i states (0,0)) (Znth (i+1) states (0,0))) ∧
      Znth (Zlength states - 1) states (0,0) = (0, x + (k : Int)*(a-b)) := by
  induction k generalizing x with
  | zero =>
    refine ⟨[(0,x)], ?_, rfl, ?_, ?_⟩
    · intro h; cases h
    · intro i hi
      change 0 ≤ i ∧ i < 0 at hi
      omega
    · change (0,x) = (0,x+0*(a-b))
      simp only [Int.zero_mul, Int.add_zero]
  | succ k ih =>
    rcases ih (x-b+a) (by omega) with ⟨states, hn, hh, ht, hl⟩
    refine ⟨(0,x) :: (1,x-b) :: states, ?_, rfl, ?_, ?_⟩
    · intro h; cases h
    · apply exchange_prepend_steps__exchange_minimum a b (0,x) (1,x-b) ((1,x-b)::states)
        (by intro h; cases h) rfl
      · exact Or.inr ⟨hx, rfl, rfl⟩
      · apply exchange_prepend_steps__exchange_minimum a b (1,x-b) (0,x-b+a) states hn hh
        · exact Or.inl ⟨by decide, rfl, rfl⟩
        · exact ht
    · rw [exchange_prepend_last__exchange_minimum _ ((1,x-b)::states) (by intro h; cases h),
        exchange_prepend_last__exchange_minimum _ states hn, hl]
      congr 1
      push_cast
      ring

theorem exchange_profitable_one_reachable__exchange_minimum (n a b : Int)
    (hab : a > b) (hb : b ≥ 1) (hn : n ≥ 1) : ReachesSilver n a b 1 := by
  rcases exchange_cycle_path__exchange_minimum a b n.toNat a (by omega) (by omega) with
    ⟨states, hs, hh, ht, hl⟩
  refine ⟨(1,0)::states, ?_, rfl, ?_, ?_⟩
  · intro h; cases h
  · apply exchange_prepend_steps__exchange_minimum a b (1,0) (0,a) states hs hh
    · exact Or.inl ⟨by decide, rfl, by omega⟩
    · exact ht
  · rw [exchange_prepend_last__exchange_minimum _ states hs, hl]
    have he : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
    rw [he]
    dsimp
    have hm := mul_nonneg (show 0 ≤ n by omega) (show 0 ≤ a-b-1 by omega)
    constructor <;> nlinarith

theorem exchange_zero_unreachable__exchange_minimum (n a b : Int)
    (hb : b ≥ 1) (hn : n ≥ 1) : ¬ ReachesSilver n a b 0 := by
  rintro ⟨states, hs, hh, ht, hf⟩
  cases states with
  | nil => contradiction
  | cons s1 rest =>
    change s1 = (0,0) at hh
    subst s1
    cases rest with
    | nil => change (0 : Int) ≥ 0 ∧ (0 : Int) ≥ n at hf; omega
    | cons s2 rest =>
      have hp := Zlength_nonneg rest
      have hx := ht 0 (by simp only [Zlength_cons]; omega)
      change ExchangeStep a b (0,0) s2 at hx
      rcases s2 with ⟨g,x⟩
      rcases hx with ⟨hh, _, _⟩ | ⟨hh, _, _⟩ <;> omega

theorem exchange_nonprofitable_spec__exchange_minimum (n a b : Int)
    (hn : 1 ≤ n) (ha : 1 ≤ a) (hab : a ≤ b) :
    Spec n a b (Z.div ((n+a)-1) a) := by
  have he : Z.div ((n+a)-1) a = ((n+a)-1) / a :=
    Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  rw [he]
  let q := ((n+a)-1) / a
  have hq : 0 ≤ q := Int.ediv_nonneg (by omega) (by omega)
  have hd := Int.lt_ediv_mul ((n+a)-1) (show 0 < a by omega)
  have hc : n ≤ a*q := by dsimp [q]; nlinarith
  refine ⟨q, ⟨⟨hq, exchange_sell_trace__exchange_minimum n a b q ha hq hc⟩, ?_⟩, rfl⟩
  intro k hk
  have hl := exchange_nonprofitable_lower_bound__exchange_minimum n a b k (by omega) hab hk.2
  have ht : ((n+a)-1) / a < k+1 :=
    Int.ediv_lt_of_lt_mul (by omega) (by nlinarith)
  dsimp [q]
  omega

theorem exchange_profitable_spec__exchange_minimum (n a b : Int)
    (hab : a > b) (hb : b ≥ 1) (hn : n ≥ 1) : Spec n a b 1 := by
  refine ⟨1, ⟨⟨by omega, exchange_profitable_one_reachable__exchange_minimum n a b hab hb hn⟩, ?_⟩, rfl⟩
  intro k hk
  have hz : k ≠ 0 := by
    intro he
    rw [he] at hk
    exact exchange_zero_unreachable__exchange_minimum n a b hb hn hk.2
  change (1 : Int) ≤ k
  omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib
