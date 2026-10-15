import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import ListLib.General.Length

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_lib
open AUXLib SimpleC.SL.IntLib

def digit_sum_modulus : Int := 1000000007

inductive Base10DigitSum : Int → Int → Prop where
  | Base10DigitSum_zero : Base10DigitSum 0 0
  | Base10DigitSum_positive (n quotient quotient_sum : Int) :
      0 < n → quotient = Z.div n 10 → Base10DigitSum quotient quotient_sum →
      Base10DigitSum n (quotient_sum + Z.modulo n 10)
export Base10DigitSum (Base10DigitSum_zero Base10DigitSum_positive)

inductive PrefixDigitSum : Int → Int → Prop where
  | PrefixDigitSum_nonpositive (x : Int) : x ≤ 0 → PrefixDigitSum x 0
  | PrefixDigitSum_positive_base : PrefixDigitSum 1 1
  | PrefixDigitSum_positive_step (x total next_digit_sum : Int) :
      1 ≤ x → PrefixDigitSum x total → Base10DigitSum (x+1) next_digit_sum →
      PrefixDigitSum (x+1) (Z.modulo (total + next_digit_sum) digit_sum_modulus)
export PrefixDigitSum (PrefixDigitSum_nonpositive PrefixDigitSum_positive_base PrefixDigitSum_positive_step)

inductive InclusiveDigitSum (lo : Int) : Int → Int → Prop where
  | InclusiveDigitSum_single (digit_sum : Int) : Base10DigitSum lo digit_sum → InclusiveDigitSum lo lo digit_sum
  | InclusiveDigitSum_extend (hi total next_digit_sum : Int) :
      lo ≤ hi → InclusiveDigitSum lo hi total → Base10DigitSum (hi+1) next_digit_sum →
      InclusiveDigitSum lo (hi+1) (total+next_digit_sum)

@[match_pattern] abbrev InclusiveDigitSum_single (lo digit_sum : Int) (h : Base10DigitSum lo digit_sum) :=
  InclusiveDigitSum.InclusiveDigitSum_single (lo := lo) digit_sum h
@[match_pattern] abbrev InclusiveDigitSum_extend (lo hi total next_digit_sum : Int) (hh : lo ≤ hi)
    (h : InclusiveDigitSum lo hi total) (hn : Base10DigitSum (hi+1) next_digit_sum) :=
  InclusiveDigitSum.InclusiveDigitSum_extend (lo := lo) hi total next_digit_sum hh h hn

def IntervalDigitSum (lo hi answer : Int) : Prop :=
  ∃ total, lo ≤ hi ∧ InclusiveDigitSum lo hi total ∧ answer = Z.modulo total digit_sum_modulus

def PowerTable (power : List Int) : Prop :=
  Zlength power = 20 ∧ ∀ i, (0 ≤ i ∧ i < 20) → Znth i power 0 = Z.modulo (Z.pow 10 i) digit_sum_modulus

def PowerPrefix (power : List Int) (hi : Int) : Prop :=
  Zlength power = hi ∧ (1 ≤ hi ∧ hi ≤ 20) ∧
  ∀ i, (0 ≤ i ∧ i < hi) → Znth i power 0 = Z.modulo (Z.pow 10 i) digit_sum_modulus

def DigitDPValue (places leading : Int) : Int :=
  if places = 1 then Z.modulo leading digit_sum_modulus else
    Z.modulo (leading * Z.pow 10 (places-1) + 45 * (places-1) * Z.pow 10 (places-2)) digit_sum_modulus

def DigitDPTable (dp : List Int) : Prop :=
  Zlength dp = 200 ∧ (∀ j, (0 ≤ j ∧ j < 10) → Znth j dp 0 = 0) ∧
  ∀ places leading, (1 ≤ places ∧ places < 20) → (0 ≤ leading ∧ leading < 10) →
    Znth (places*10+leading) dp 0 = DigitDPValue places leading

def ZeroSegment (values : List Int) (hi total : Int) : Prop :=
  Zlength values = hi ∧ (0 ≤ hi ∧ hi ≤ total) ∧ ∀ k, (0 ≤ k ∧ k < hi) → Znth k values 0 = 0

def DigitDPBaseProgress (dp : List Int) (next : Int) : Prop :=
  Zlength dp = 200 ∧ (0 ≤ next ∧ next ≤ 10) ∧
  (∀ j, (0 ≤ j ∧ j < next) → Znth (10+j) dp 0 = j) ∧
  ∀ k, (0 ≤ k ∧ k < 200) → (k < 10 ∨ 20 ≤ k ∨ 10+next ≤ k) → Znth k dp 0 = 0

def DigitDPOuterProgress (dp : List Int) (next_places : Int) : Prop :=
  Zlength dp = 200 ∧ (2 ≤ next_places ∧ next_places ≤ 20) ∧
  (∀ d, (0 ≤ d ∧ d < 10) → Znth d dp 0 = 0) ∧
  (∀ places leading, (1 ≤ places ∧ places < next_places) → (0 ≤ leading ∧ leading < 10) →
    Znth (places*10+leading) dp 0 = DigitDPValue places leading) ∧
  ∀ places leading, (next_places ≤ places ∧ places < 20) → (0 ≤ leading ∧ leading < 10) →
    Znth (places*10+leading) dp 0 = 0

def DigitDPRowProgress (dp : List Int) (places next_leading : Int) : Prop :=
  Zlength dp = 200 ∧ (2 ≤ places ∧ places < 20) ∧ (0 ≤ next_leading ∧ next_leading ≤ 10) ∧
  (∀ d, (0 ≤ d ∧ d < 10) → Znth d dp 0 = 0) ∧
  (∀ p d, (1 ≤ p ∧ p < places) → (0 ≤ d ∧ d < 10) → Znth (p*10+d) dp 0 = DigitDPValue p d) ∧
  (∀ d, (0 ≤ d ∧ d < next_leading) → Znth (places*10+d) dp 0 = DigitDPValue places d) ∧
  (∀ d, (next_leading ≤ d ∧ d < 10) → Znth (places*10+d) dp 0 = 0) ∧
  ∀ p d, (places < p ∧ p < 20) → (0 ≤ d ∧ d < 10) → Znth (p*10+d) dp 0 = 0

inductive InnerCandidateDigitSum (dp : List Int) (places : Int) : Int → Int → Prop where
  | InnerCandidateDigitSum_zero : InnerCandidateDigitSum dp places 0 0
  | InnerCandidateDigitSum_step (next «partial» : Int) :
      0 ≤ next → InnerCandidateDigitSum dp places next «partial» →
      InnerCandidateDigitSum dp places (next+1)
        (Z.modulo («partial» + Znth (places*10+next) dp 0) digit_sum_modulus)
@[match_pattern] abbrev InnerCandidateDigitSum_zero (dp : List Int) (places : Int) :=
  InnerCandidateDigitSum.InnerCandidateDigitSum_zero (dp := dp) (places := places)
@[match_pattern] abbrev InnerCandidateDigitSum_step (dp : List Int) (places next «partial» : Int)
    (hn : 0 ≤ next) (h : InnerCandidateDigitSum dp places next «partial») :=
  InnerCandidateDigitSum.InnerCandidateDigitSum_step (dp := dp) (places := places) next «partial» hn h

def DigitDPCellProgress (dp : List Int) (places leading next_suffix : Int) : Prop :=
  Zlength dp = 200 ∧ (2 ≤ places ∧ places < 20) ∧ (0 ≤ leading ∧ leading < 10) ∧
  (0 ≤ next_suffix ∧ next_suffix ≤ 10) ∧
  (∀ d, (0 ≤ d ∧ d < 10) → Znth d dp 0 = 0) ∧
  (∀ p d, (1 ≤ p ∧ p < places) → (0 ≤ d ∧ d < 10) → Znth (p*10+d) dp 0 = DigitDPValue p d) ∧
  (∀ d, (0 ≤ d ∧ d < leading) → Znth (places*10+d) dp 0 = DigitDPValue places d) ∧
  (∀ d, (leading < d ∧ d < 10) → Znth (places*10+d) dp 0 = 0) ∧
  (∀ p d, (places < p ∧ p < 20) → (0 ≤ d ∧ d < 10) → Znth (p*10+d) dp 0 = 0) ∧
  ∃ «partial», InnerCandidateDigitSum dp (places-1) next_suffix «partial» ∧
    Znth (places*10+leading) dp 0 = Z.modulo («partial» + next_suffix * Z.pow 10 (places-2) * leading) digit_sum_modulus

def ExtractedDigitBuffer (x : Int) (digits : List Int) (count remaining : Int) : Prop :=
  Zlength digits = 20 ∧ (0 ≤ count ∧ count ≤ 19) ∧ remaining = Z.div x (Z.pow 10 count) ∧
  (∀ k, (1 ≤ k ∧ k ≤ count) → Znth k digits 0 = Z.modulo (Z.div x (Z.pow 10 (k-1))) 10) ∧
  ∀ k, (count < k ∧ k < 20) → Znth k digits 0 = 0

def ExtractedDigitCount (x count : Int) : Prop :=
  (1 ≤ count ∧ count ≤ 19) ∧ (Z.pow 10 (count-1) ≤ x ∧ x < Z.pow 10 count)

def DigitPositionPower (position power : Int) : Prop :=
  (1 ≤ position ∧ position ≤ 19) ∧ power = Z.pow 10 (position-1)

def OuterDigitPositionPower (position power : Int) : Prop :=
  (position = 0 ∧ power = 0) ∨ ((1 ≤ position ∧ position ≤ 19) ∧ power = Z.pow 10 (position-1))

def AccumulatedDigitSumCorrect (x position answer : Int) : Prop :=
  (position = 0 ∧ PrefixDigitSum x answer) ∨
  (1 ≤ position ∧ ∃ high high_digit_sum before, high = Z.div x (Z.pow 10 position) ∧
    Base10DigitSum high high_digit_sum ∧ PrefixDigitSum (high-1) before ∧
    answer = Z.modulo (Z.pow 10 position * before + 45 * high * position * Z.pow 10 (position-1) +
      (Z.modulo x (Z.pow 10 position)+1)*high_digit_sum) digit_sum_modulus)

inductive DigitPositionAccumulation (x : Int) (dp digits : List Int) : Int → Int → Prop where
  | DigitPositionAccumulation_start (count : Int) :
      ExtractedDigitBuffer x digits count 0 → ExtractedDigitCount x count →
      DigitPositionAccumulation x dp digits count 0
  | DigitPositionAccumulation_step (places answer choice_sum : Int) :
      1 ≤ places → DigitPositionAccumulation x dp digits places answer →
      InnerCandidateDigitSum dp places (Znth places digits 0) choice_sum →
      DigitPositionAccumulation x dp digits (places-1)
        (Z.modulo (answer + choice_sum + Z.modulo (Z.modulo x (Z.pow 10 (places-1))+1) digit_sum_modulus *
          Znth places digits 0) digit_sum_modulus)
@[match_pattern] abbrev DigitPositionAccumulation_start (x : Int) (dp digits : List Int) (count : Int)
    (hb : ExtractedDigitBuffer x digits count 0) (hc : ExtractedDigitCount x count) :=
  DigitPositionAccumulation.DigitPositionAccumulation_start (x := x) (dp := dp) (digits := digits) count hb hc
@[match_pattern] abbrev DigitPositionAccumulation_step (x : Int) (dp digits : List Int) (places answer choice_sum : Int)
    (hp : 1 ≤ places) (h : DigitPositionAccumulation x dp digits places answer)
    (hs : InnerCandidateDigitSum dp places (Znth places digits 0) choice_sum) :=
  DigitPositionAccumulation.DigitPositionAccumulation_step (x := x) (dp := dp) (digits := digits) places answer choice_sum hp h hs

def OuterDigitPositionProgress (x : Int) (dp digits : List Int) (position answer : Int) : Prop :=
  DigitPositionAccumulation x dp digits position answer

def InnerCandidateDigitProgressLegacy (x : Int) (dp digits : List Int) (places next_digit answer_before answer : Int) : Prop :=
  (1 ≤ places ∧ places ≤ 19) ∧ (0 ≤ next_digit ∧ next_digit ≤ Znth places digits 0) ∧
  OuterDigitPositionProgress x dp digits places answer_before ∧ ∃ choice_sum,
    InnerCandidateDigitSum dp places next_digit choice_sum ∧ answer = Z.modulo (answer_before + choice_sum) digit_sum_modulus

def CompletedDigitPositionScan (x : Int) (dp digits : List Int) (answer : Int) : Prop :=
  OuterDigitPositionProgress x dp digits 0 answer

private theorem mod_bounds (x : Int) :
    0 ≤ Z.modulo x digit_sum_modulus ∧ Z.modulo x digit_sum_modulus < digit_sum_modulus :=
  ⟨Int.fmod_nonneg_of_pos _ (by decide), Int.fmod_lt_of_pos _ (by decide)⟩

private theorem pow_step (a n : Int) (hn : 0 ≤ n) : Z.pow a (n+1) = Z.pow a n * a := by
  cases n with
  | ofNat n => exact Int.pow_succ a n
  | negSucc n => omega

private theorem pow10_pos (n : Int) (hn : 0 ≤ n) : 0 < Z.pow 10 n := by
  cases n with
  | ofNat n => exact Int.pow_pos (by decide : (0 : Int) < 10)
  | negSucc n => omega

private theorem mul_mod_left (a b m : Int) :
    Z.modulo (Z.modulo a m * b) m = Z.modulo (a*b) m := by
  unfold Z.modulo
  rw [Int.mul_fmod, Int.fmod_fmod, ← Int.mul_fmod]

theorem Znth_app_left__digits_power_and_zero_init (l1 l2 : List Int) (d i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l1) : Znth i (l1 ++ l2) d = Znth i l1 d :=
  ListLib.app_Znth1 d l1 l2 i hi

theorem Znth_app_last__digits_power_and_zero_init (l : List Int) (d x : Int) :
    Znth (Zlength l) (l ++ [x]) d = x := by
  rw [app_Znth2 d l [x] (Zlength l) (Int.le_refl _)]
  simp

theorem ZeroSegment_app_zero__digits_power_and_zero_init (values : List Int) (hi total : Int)
    (hz : ZeroSegment values hi total) (hl : hi < total) : ZeroSegment (values ++ [0]) (hi+1) total := by
  refine ⟨by simp only [Zlength_app, Zlength_cons, Zlength_nil, hz.1]; omega, ⟨by have := hz.2.1; omega, by omega⟩, ?_⟩
  have hlen := hz.1
  intro k hk
  by_cases hlt : k < hi
  · rw [Znth_app_left__digits_power_and_zero_init values [0] 0 k (by omega)]
    exact hz.2.2 k (by omega)
  · have he : k = Zlength values := by omega
    rw [he, Znth_app_last__digits_power_and_zero_init]

private theorem dp_value_bounds (places leading : Int) :
    0 ≤ DigitDPValue places leading ∧ DigitDPValue places leading < digit_sum_modulus := by
  unfold DigitDPValue
  split <;> apply mod_bounds

theorem digits_dp_previous_term_bounds__digits_dp_cell (power_l dp_l : List Int) (k j i : Int)
    (hk10 : k < 10) (hi2 : 2 ≤ i) (hi20 : i < 20) (hj0 : 0 ≤ j) (hj10 : j < 10)
    (hk0 : 0 ≤ k) (hkle : k ≤ 10) (hc : DigitDPCellProgress dp_l i j k) (hp : PowerTable power_l) :
    0 ≤ Znth ((i-1)*10+k) dp_l 0 + Z.rem (Znth (i-2) power_l 0 * j) 1000000007 ∧
    Znth ((i-1)*10+k) dp_l 0 + Z.rem (Znth (i-2) power_l 0 * j) 1000000007 < 1000000007+1000000007 := by
  have hv := hc.2.2.2.2.2.1 (i-1) k (by omega) (by omega)
  have hpow := hp.2 (i-2) (by omega)
  have hb := dp_value_bounds (i-1) k
  have hm := mod_bounds (Z.pow 10 (i-2))
  have hprod : 0 ≤ Znth (i-2) power_l 0 * j := Int.mul_nonneg (by omega) hj0
  have hr := rem_nonneg_bounds (Znth (i-2) power_l 0 * j) 1000000007 hprod (by decide)
  unfold digit_sum_modulus at *
  omega

theorem digits_dp_current_plus_moving_bounds__digits_dp_cell (power_l dp_l : List Int) (k j i : Int)
    (hk10 : k < 10) (hi2 : 2 ≤ i) (hi20 : i < 20) (hj0 : 0 ≤ j) (hj10 : j < 10)
    (hk0 : 0 ≤ k) (hkle : k ≤ 10) (hc : DigitDPCellProgress dp_l i j k) (hp : PowerTable power_l) :
    0 ≤ Znth (i*10+j) dp_l 0 + Z.rem
      (Znth ((i-1)*10+k) dp_l 0 + Z.rem (Znth (i-2) power_l 0 * j) 1000000007) 1000000007 ∧
    Znth (i*10+j) dp_l 0 + Z.rem
      (Znth ((i-1)*10+k) dp_l 0 + Z.rem (Znth (i-2) power_l 0 * j) 1000000007) 1000000007 < 1000000007+1000000007 := by
  have hnum := digits_dp_previous_term_bounds__digits_dp_cell power_l dp_l k j i hk10 hi2 hi20 hj0 hj10 hk0 hkle hc hp
  obtain ⟨part, hinner, hcur⟩ := hc.2.2.2.2.2.2.2.2.2
  have hcurbounds := mod_bounds (part + k * Z.pow 10 (i-2) * j)
  have hr := rem_nonneg_bounds _ 1000000007 hnum.1 (by decide)
  unfold digit_sum_modulus at *
  omega

theorem Zlength_replace_Znth__digits_dp_cell {A : Type} (i : Int) (x : A) (l : List A) :
    Zlength (replace_Znth i x l) = Zlength l := Zlength_replace_Znth l i x

theorem InnerCandidateDigitSum_replace_other__digits_dp_cell (dp : List Int) (places count part idx value : Int)
    (hi : 0 ≤ idx ∧ idx < Zlength dp)
    (ha : ∀ next, (0 ≤ next ∧ next < count) →
      (0 ≤ places*10+next ∧ places*10+next < Zlength dp) ∧ places*10+next ≠ idx)
    (hs : InnerCandidateDigitSum dp places count part) :
    InnerCandidateDigitSum (replace_Znth idx value dp) places count part := by
  induction hs with
  | InnerCandidateDigitSum_zero => exact .InnerCandidateDigitSum_zero
  | InnerCandidateDigitSum_step next part hn hs ih =>
    have haw := ha next (by omega)
    rw [← Znth_replace_Znth_Diff 0 dp idx (places*10+next) value hi haw.1 (Ne.symm haw.2)]
    exact .InnerCandidateDigitSum_step next part hn (ih (by intro next' hnext'; exact ha next' (by omega)))

theorem digit_dp_cell_mod_update__digits_dp_cell (a b p k j modulus : Int) (hm : modulus ≠ 0) :
    Z.modulo (Z.modulo (a+k*p*j) modulus + Z.modulo (b + Z.modulo (Z.modulo p modulus*j) modulus) modulus) modulus =
    Z.modulo (Z.modulo (a+b) modulus + (k+1)*p*j) modulus := by
  rw [mul_mod_left]
  unfold Z.modulo
  simp only [Int.fmod_add_fmod, Int.add_fmod_fmod]
  congr 1
  grind

theorem InnerCandidateDigitSum_next_inv__digits_dp_row (dp : List Int) (places next total : Int)
    (hn : 0 ≤ next) (hs : InnerCandidateDigitSum dp places (next+1) total) :
    ∃ part, InnerCandidateDigitSum dp places next part ∧
      total = Z.modulo (part + Znth (places*10+next) dp 0) digit_sum_modulus := by
  generalize he : next+1 = count at hs
  cases hs with
  | InnerCandidateDigitSum_zero => omega
  | InnerCandidateDigitSum_step next' part hn' hs =>
    have h : next' = next := by omega
    subst next'
    exact ⟨part, hs, rfl⟩

theorem InnerCandidateDigitSum_formula_ge2__digits_dp_row (dp : List Int) (places next part : Int)
    (hp : 2 ≤ places)
    (hv : ∀ d, (0 ≤ d ∧ d < next) → Znth (places*10+d) dp 0 = DigitDPValue places d)
    (hs : InnerCandidateDigitSum dp places next part) :
    part = Z.modulo (5*next*(next-1)*Z.pow 10 (places-2) +
      next*45*(places-1)*Z.pow 10 (places-2)) digit_sum_modulus := by
  induction hs with
  | InnerCandidateDigitSum_zero => simp [Z.modulo]
  | InnerCandidateDigitSum_step next part hn hs ih =>
    have ih := ih (by intro d hd; exact hv d (by omega))
    rw [hv next (by omega), DigitDPValue, if_neg (by omega), ih]
    have he : places - 1 = places - 2 + 1 := by omega
    rw [he, pow_step 10 (places-2) (by omega)]
    unfold Z.modulo
    rw [Int.fmod_add_fmod, Int.add_fmod_fmod]
    congr 1
    grind

theorem signed_last_nbits_small (x n : Int) (hn : n > 0)
    (hx : 0 ≤ x ∧ x < Z.pow 2 (n-1)) : signed_last_nbits x n = x := by
  apply signed_last_nbits_eq x n hn
  omega

theorem DigitDPValue_nonnegative__prefix_inner_outer_scan (places leading : Int) :
    0 ≤ DigitDPValue places leading := (dp_value_bounds places leading).1

theorem outer_power_predecessor__prefix_inner_outer_scan (i power : Int)
    (hi : 1 ≤ i) (hp : OuterDigitPositionPower i power) :
    OuterDigitPositionPower (i-1) (Z.quot power 10) := by
  rcases hp with ⟨hz, _⟩ | ⟨hr, rfl⟩
  · omega
  · by_cases he : i = 1
    · subst i; exact Or.inl ⟨rfl, rfl⟩
    · refine Or.inr ⟨⟨by omega, by omega⟩, ?_⟩
      rw [show i-1 = i-2+1 by omega, pow_step 10 (i-2) (by omega), Z.quot_mul _ 10 (by decide)]
      congr 1
      omega

theorem signed_modulus_range__prefix_inner_outer_scan (value : Int) :
    0 ≤ signed_last_nbits (Z.modulo value 1000000007) 32 ∧
    signed_last_nbits (Z.modulo value 1000000007) 32 < 1000000007 := by
  have hb := mod_bounds value
  rw [signed_last_nbits_eq _ 32 (by decide) (by change -2147483648 ≤ _ ∧ _ < 2147483648; unfold digit_sum_modulus at hb; omega)]
  exact hb

theorem interval_answer_upper__interval_bridge (retval retval_2 : Int) :
    Z.modulo (Z.rem (retval-retval_2) digit_sum_modulus + digit_sum_modulus) digit_sum_modulus < digit_sum_modulus :=
  (mod_bounds _).2

theorem interval_answer_lower__interval_bridge (retval retval_2 : Int) :
    0 ≤ Z.modulo (Z.rem (retval-retval_2) digit_sum_modulus + digit_sum_modulus) digit_sum_modulus :=
  (mod_bounds _).1

theorem normalized_outer_rem__interval_bridge (value : Int) :
    Z.rem (Z.rem value digit_sum_modulus+digit_sum_modulus) digit_sum_modulus =
    Z.modulo (Z.rem value digit_sum_modulus+digit_sum_modulus) digit_sum_modulus := by
  have hr := rem_bounds value digit_sum_modulus (by decide)
  exact rem_eq_mod _ _ (by omega) (by decide)

theorem normalized_rem_mod__interval_bridge (value : Int) :
    Z.modulo (Z.rem value digit_sum_modulus+digit_sum_modulus) digit_sum_modulus = Z.modulo value digit_sum_modulus := by
  have hr := Int.tmod_add_tdiv_mul value digit_sum_modulus
  change Z.rem value digit_sum_modulus + Z.quot value digit_sum_modulus * digit_sum_modulus = value at hr
  have he : Z.rem value digit_sum_modulus + digit_sum_modulus =
      value+(1-Z.quot value digit_sum_modulus)*digit_sum_modulus := by grind
  rw [he]
  exact Int.add_mul_fmod_self_right _ _ _

theorem Base10DigitSum_deterministic__interval_bridge (n first second : Int)
    (hf : Base10DigitSum n first) (hs : Base10DigitSum n second) : first = second := by
  have hgen : ∀ n' second, n = n' → Base10DigitSum n' second → first = second := by
    clear hs
    induction hf with
    | Base10DigitSum_zero =>
      intro n' second he h
      cases h with
      | Base10DigitSum_zero => rfl
      | Base10DigitSum_positive x q qs hx hq hqs => omega
    | Base10DigitSum_positive x q qs hx hq hqs ih =>
      intro n' second he h
      cases h with
      | Base10DigitSum_zero => omega
      | Base10DigitSum_positive y r rs hy hr hrs =>
        subst n'
        have hqr : q = r := by omega
        have hsum := ih r rs hqr hrs
        omega
  exact hgen n second rfl hs

theorem PrefixDigitSum_deterministic__interval_bridge (n first second : Int)
    (hf : PrefixDigitSum n first) (hs : PrefixDigitSum n second) : first = second := by
  have hgen : ∀ n' second, n = n' → PrefixDigitSum n' second → first = second := by
    clear hs
    induction hf with
    | PrefixDigitSum_nonpositive x hx =>
      intro n' second he h
      cases h with
      | PrefixDigitSum_nonpositive y hy => rfl
      | PrefixDigitSum_positive_base => omega
      | PrefixDigitSum_positive_step y total ds hy ht hd => omega
    | PrefixDigitSum_positive_base =>
      intro n' second he h
      cases h with
      | PrefixDigitSum_nonpositive y hy => omega
      | PrefixDigitSum_positive_base => rfl
      | PrefixDigitSum_positive_step y total ds hy ht hd => omega
    | PrefixDigitSum_positive_step x total ds hx ht hd ih =>
      intro n' second he h
      cases h with
      | PrefixDigitSum_nonpositive y hy => omega
      | PrefixDigitSum_positive_base => omega
      | PrefixDigitSum_positive_step y total' ds' hy ht' hd' =>
        have hxy : y = x := by omega
        subst y
        have htotal := ih x total' rfl ht'
        have hds := Base10DigitSum_deterministic__interval_bridge (x+1) ds ds' hd hd'
        rw [htotal, hds]
  exact hgen n second rfl hs

private theorem digit_one : Base10DigitSum 1 1 :=
  Base10DigitSum_positive 1 0 0 (by decide) rfl Base10DigitSum_zero

theorem PrefixDigitSum_interval_bridge__interval_bridge (lo hi before after : Int)
    (hlo : 1 ≤ lo) (hle : lo ≤ hi) (hb : PrefixDigitSum (lo-1) before) (ha : PrefixDigitSum hi after) :
    ∃ total, InclusiveDigitSum lo hi total ∧ after = Z.modulo (before+total) digit_sum_modulus := by
  induction ha with
  | PrefixDigitSum_nonpositive x hx => omega
  | PrefixDigitSum_positive_base =>
    have he : lo = 1 := by omega
    subst lo
    have hz := PrefixDigitSum_deterministic__interval_bridge 0 before 0 hb (PrefixDigitSum_nonpositive 0 (by decide))
    subst before
    exact ⟨1, InclusiveDigitSum_single 1 1 digit_one, rfl⟩
  | PrefixDigitSum_positive_step x total ds hx ht hd ih =>
    by_cases he : lo = x+1
    · have hbefore : before = total :=
        PrefixDigitSum_deterministic__interval_bridge x before total
          (by simpa only [he, Int.add_sub_cancel] using hb) ht
      refine ⟨ds, ?_, ?_⟩
      · rw [he]; exact InclusiveDigitSum_single (x+1) ds hd
      · rw [hbefore]
    · obtain ⟨range_total, hr, hv⟩ := ih (by omega)
      refine ⟨range_total+ds, InclusiveDigitSum_extend lo x range_total ds (by omega) hr hd, ?_⟩
      rw [hv]
      unfold Z.modulo
      rw [Int.fmod_add_fmod]
      congr 1
      omega

theorem IntervalDigitSum_from_prefixes__interval_bridge (lo hi before after : Int)
    (hlo : 1 ≤ lo) (hle : lo ≤ hi) (hb : PrefixDigitSum (lo-1) before) (ha : PrefixDigitSum hi after) :
    IntervalDigitSum lo hi (Z.modulo (Z.rem (after-before) digit_sum_modulus+digit_sum_modulus) digit_sum_modulus) := by
  obtain ⟨total, hr, he⟩ := PrefixDigitSum_interval_bridge__interval_bridge lo hi before after hlo hle hb ha
  refine ⟨total, hle, hr, ?_⟩
  rw [normalized_rem_mod__interval_bridge, he]
  unfold Z.modulo
  rw [show (before+total).fmod digit_sum_modulus-before = (before+total).fmod digit_sum_modulus + -before by omega,
    Int.fmod_add_fmod]
  congr 1
  omega

theorem PrefixDigitSum_range (x total : Int) (hs : PrefixDigitSum x total) :
    0 ≤ total ∧ total < digit_sum_modulus := by
  cases hs with
  | PrefixDigitSum_nonpositive x hx => decide
  | PrefixDigitSum_positive_base => decide
  | PrefixDigitSum_positive_step x total ds hx ht hd => exact mod_bounds _

theorem Base10DigitSum_append_digit (high digit high_sum : Int)
    (hh : 0 ≤ high) (hd : 0 ≤ digit ∧ digit < 10) (hs : Base10DigitSum high high_sum) :
    Base10DigitSum (10*high+digit) (high_sum+digit) := by
  by_cases hz : 10*high+digit = 0
  · have hh0 : high = 0 := by omega
    have hd0 : digit = 0 := by omega
    subst high digit
    have hsum := Base10DigitSum_deterministic__interval_bridge 0 high_sum 0 hs Base10DigitSum_zero
    subst high_sum
    exact Base10DigitSum_zero
  · have hm : Z.modulo (10*high+digit) 10 = digit := by
      change (10*high+digit).fmod 10 = digit
      rw [Int.mul_add_fmod_self_left, Int.fmod_eq_of_lt hd.1 hd.2]
    have hq : high = Z.div (10*high+digit) 10 := by
      have he := Int.fmod_add_mul_fdiv (10*high+digit) 10
      change (10*high+digit).fmod 10 = digit at hm
      unfold Z.div
      omega
    simpa only [hm] using Base10DigitSum_positive _ high high_sum (by omega) hq hs

theorem PrefixDigitSum_predecessor (n total : Int) (hn : 1 ≤ n) (hs : PrefixDigitSum n total) :
    ∃ before digit_sum, PrefixDigitSum (n-1) before ∧ Base10DigitSum n digit_sum ∧
      total = Z.modulo (before+digit_sum) digit_sum_modulus := by
  cases hs with
  | PrefixDigitSum_nonpositive x hx => omega
  | PrefixDigitSum_positive_base =>
    exact ⟨0, 1, PrefixDigitSum_nonpositive 0 (by decide), digit_one, rfl⟩
  | PrefixDigitSum_positive_step x total ds hx ht hd =>
    refine ⟨total, ds, ?_, hd, rfl⟩
    simpa only [Int.add_sub_cancel] using ht

private theorem inner_one_formula (dp : List Int) (digit part : Int)
    (hv : ∀ d, (0 ≤ d ∧ d < 10) → Znth (1*10+d) dp 0 = DigitDPValue 1 d)
    (hs : InnerCandidateDigitSum dp 1 digit part) :
    ∀ triangle, (0 ≤ digit ∧ digit ≤ 10) → 2*triangle = digit*(digit-1) →
      part = Z.modulo triangle digit_sum_modulus := by
  induction hs with
  | InnerCandidateDigitSum_zero =>
    intro triangle hd ht
    have : triangle = 0 := by omega
    subst triangle
    rfl
  | InnerCandidateDigitSum_step next part hn hs ih =>
    intro triangle hd ht
    have htprev : 2*(triangle-next) = next*(next-1) := by grind
    rw [hv next (by omega)]
    have hval : DigitDPValue 1 next = next := by
      simp only [DigitDPValue, if_pos rfl]
      exact Int.fmod_eq_of_lt hn (by unfold digit_sum_modulus; omega)
    rw [hval, ih (triangle-next) (by omega) htprev]
    change ((triangle-next).fmod digit_sum_modulus + next).fmod digit_sum_modulus = _
    rw [Int.fmod_add_fmod]
    congr 1
    omega

theorem InnerCandidateDigitSum_one_formula (dp : List Int) (digit part triangle : Int)
    (hd : 0 ≤ digit ∧ digit < 10) (ht : 2*triangle = digit*(digit-1))
    (hv : DigitDPTable dp) (hs : InnerCandidateDigitSum dp 1 digit part) :
    part = Z.modulo triangle digit_sum_modulus :=
  inner_one_formula dp digit part (fun d hd => hv.2.2 1 d (by omega) hd) hs triangle (by omega) ht

theorem InnerCandidateDigitSum_ten__digits_dp_row (dp : List Int) (places part : Int)
    (hp : 1 ≤ places)
    (hv : ∀ d, (0 ≤ d ∧ d < 10) → Znth (places*10+d) dp 0 = DigitDPValue places d)
    (hs : InnerCandidateDigitSum dp places 10 part) :
    part = Z.modulo (45*places*Z.pow 10 (places-1)) digit_sum_modulus := by
  by_cases he : places = 1
  · subst places
    exact inner_one_formula dp 10 part hv hs 45 (by omega) (by decide)
  · have hf := InnerCandidateDigitSum_formula_ge2__digits_dp_row dp places 10 part (by omega) hv hs
    rw [hf, show places-1 = places-2+1 by omega, pow_step 10 (places-2) (by omega)]
    congr 1
    grind

theorem mod_program_update (first second low digit modulus : Int) (hm : modulus ≠ 0) :
    Z.modulo (Z.modulo first modulus + Z.modulo second modulus + Z.modulo low modulus * digit) modulus =
      Z.modulo (first + second + low*digit) modulus := by
  unfold Z.modulo
  rw [Int.add_fmod (first.fmod modulus + second.fmod modulus) (low.fmod modulus*digit) modulus]
  rw [show (first.fmod modulus + second.fmod modulus).fmod modulus = (first+second).fmod modulus by
    rw [Int.fmod_add_fmod, Int.add_fmod_fmod]]
  rw [show (low.fmod modulus*digit).fmod modulus = (low*digit).fmod modulus from mul_mod_left low digit modulus]
  exact (Int.add_fmod (first+second) (low*digit) modulus).symm

theorem mod_scaled_add (scale base rest modulus : Int) (hm : modulus ≠ 0) :
    Z.modulo (scale * Z.modulo base modulus + rest) modulus = Z.modulo (scale*base+rest) modulus := by
  unfold Z.modulo
  rw [Int.add_fmod, Int.mul_comm scale (base.fmod modulus),
    show (base.fmod modulus*scale).fmod modulus = (base*scale).fmod modulus from mul_mod_left base scale modulus,
    Int.mul_comm base scale, ← Int.add_fmod]

theorem AccumulatedDigitSumCorrect_initial (x count : Int) (hx : 1 ≤ x) (hc : ExtractedDigitCount x count) :
    AccumulatedDigitSumCorrect x count 0 := by
  refine Or.inr ⟨hc.1.1, 0, 0, 0, ?_, .Base10DigitSum_zero, .PrefixDigitSum_nonpositive (0-1) (by decide), ?_⟩
  · exact (Int.fdiv_eq_zero_of_lt (by omega) hc.2.2).symm
  · simp only [Int.mul_zero, Int.zero_mul, Int.add_zero]
    rfl

theorem PrefixDigitSum_append_decimal_digits (high count high_sum start triangle : Int)
    (hh : 0 < high) (hc : 0 ≤ count ∧ count ≤ 10) (ht : 2*triangle = count*(count-1))
    (hs : Base10DigitSum high high_sum) (hp : PrefixDigitSum (10*high-1) start) :
    PrefixDigitSum (10*high+count-1) (Z.modulo (start+count*high_sum+triangle) digit_sum_modulus) := by
  have hgen : ∀ n : Nat, ∀ tri : Int, (n : Int) ≤ 10 → 2*tri=(n : Int)*((n : Int)-1) →
      PrefixDigitSum (10*high+(n : Int)-1) (Z.modulo (start+(n : Int)*high_sum+tri) digit_sum_modulus) := by
    intro n
    induction n with
    | zero =>
      intro tri hn ht
      have : tri = 0 := by simp only [Int.natCast_zero, Int.zero_mul] at ht; omega
      subst tri
      simpa only [Int.natCast_zero, Int.zero_mul, Int.add_zero, Z.modulo,
        Int.fmod_eq_of_lt (PrefixDigitSum_range _ _ hp).1 (PrefixDigitSum_range _ _ hp).2] using hp
    | succ n ih =>
      intro tri hn ht
      simp only [Int.natCast_succ] at hn ht ⊢
      have htprev : 2*(tri-(n : Int)) = (n : Int)*((n : Int)-1) := by grind
      have hprev := ih (tri-(n : Int)) (by omega) htprev
      have hd := Base10DigitSum_append_digit high n high_sum (by omega) (by omega) hs
      have he : 10*high+(n : Int) = (10*high+(n : Int)-1)+1 := by omega
      rw [he] at hd
      have hstep := PrefixDigitSum_positive_step (10*high+(n : Int)-1) _ (high_sum+n) (by omega) hprev hd
      have hsum : Z.modulo (Z.modulo (start+(n : Int)*high_sum+(tri-(n : Int))) digit_sum_modulus + (high_sum+(n : Int))) digit_sum_modulus =
          Z.modulo (start+((n : Int)+1)*high_sum+tri) digit_sum_modulus := by
        unfold Z.modulo
        rw [Int.fmod_add_fmod]
        congr 1
        grind
      rw [hsum] at hstep
      simpa only [show 10*high+(n : Int)-1+1 = 10*high+((n : Int)+1)-1 by omega] using hstep
  have hcn : (count.toNat : Int) = count := by omega
  simpa only [hcn] using hgen count.toNat triangle (by omega) (by simpa only [hcn] using ht)

theorem PrefixDigitSum_small_decimal_block (count triangle : Int)
    (hc : 0 ≤ count ∧ count ≤ 10) (ht : 2*triangle = count*(count-1)) :
    PrefixDigitSum (count-1) (Z.modulo triangle digit_sum_modulus) := by
  have hgen : ∀ n : Nat, ∀ tri : Int, (n : Int) ≤ 10 → 2*tri=(n : Int)*((n : Int)-1) →
      PrefixDigitSum ((n : Int)-1) (Z.modulo tri digit_sum_modulus) := by
    intro n
    induction n with
    | zero =>
      intro tri hn ht
      have : tri = 0 := by simp only [Int.natCast_zero, Int.zero_mul] at ht; omega
      subst tri
      exact .PrefixDigitSum_nonpositive (-1) (by decide)
    | succ n ih =>
      intro tri hn ht
      simp only [Int.natCast_succ] at hn ht ⊢
      by_cases hz : n = 0
      · subst n
        have : tri = 0 := by simp only [Int.natCast_zero] at ht; omega
        subst tri
        exact .PrefixDigitSum_nonpositive 0 (by decide)
      · by_cases ho : n = 1
        · subst n
          have : tri = 1 := by simp only [Int.natCast_one] at ht; omega
          subst tri
          exact .PrefixDigitSum_positive_base
        · have htprev : 2*(tri-(n : Int)) = (n : Int)*((n : Int)-1) := by grind
          have hprev := ih (tri-(n : Int)) (by omega) htprev
          have hd := Base10DigitSum_append_digit 0 n 0 (by decide) (by omega) .Base10DigitSum_zero
          simp only [Int.mul_zero, Int.zero_mul, Int.zero_add] at hd
          have hde : (n : Int) = (n : Int)-1+1 := by omega
          have hstep := PrefixDigitSum_positive_step ((n : Int)-1) _ (n : Int) (by omega) hprev (by simpa only [Int.sub_add_cancel] using hd)
          have he : Z.modulo (Z.modulo (tri-(n : Int)) digit_sum_modulus+(n : Int)) digit_sum_modulus = Z.modulo tri digit_sum_modulus := by
            unfold Z.modulo
            rw [Int.fmod_add_fmod]
            congr 1
            omega
          rw [he] at hstep
          simpa only [show (n : Int)-1+1 = (n : Int)+1-1 by omega] using hstep
  have hcn : (count.toNat : Int) = count := by omega
  simpa only [hcn] using hgen count.toNat triangle (by omega) (by simpa only [hcn] using ht)

theorem PrefixDigitSum_decimal_block (high count high_sum before triangle : Int)
    (hh : 0 ≤ high) (hc : 0 ≤ count ∧ count ≤ 10) (ht : 2*triangle = count*(count-1))
    (hs : Base10DigitSum high high_sum) (hp : PrefixDigitSum (high-1) before) :
    PrefixDigitSum (10*high+count-1)
      (Z.modulo (10*before+45*high+count*high_sum+triangle) digit_sum_modulus) := by
  have hgen : ∀ n : Nat, ∀ c s b t : Int,
      (0 ≤ c ∧ c ≤ 10) → 2*t=c*(c-1) → Base10DigitSum (n : Int) s → PrefixDigitSum ((n : Int)-1) b →
      PrefixDigitSum (10*(n : Int)+c-1) (Z.modulo (10*b+45*(n : Int)+c*s+t) digit_sum_modulus) := by
    intro n
    induction n with
    | zero =>
      intro c s b t hc ht hs hp
      have he : s = 0 := Base10DigitSum_deterministic__interval_bridge 0 s 0 hs .Base10DigitSum_zero
      have hb : b = 0 := PrefixDigitSum_deterministic__interval_bridge _ b 0 hp (.PrefixDigitSum_nonpositive _ (by decide))
      subst s; subst b
      simpa only [Int.natCast_zero, Int.mul_zero, Int.zero_add] using PrefixDigitSum_small_decimal_block c t hc ht
    | succ n ih =>
      intro c s b t hc ht hs hp
      simp only [Int.natCast_succ, Int.add_sub_cancel] at hp hs ⊢
      have hprev : ∃ pb ps, PrefixDigitSum ((n : Int)-1) pb ∧ Base10DigitSum n ps ∧ b = Z.modulo (pb+ps) digit_sum_modulus := by
        by_cases hz : n = 0
        · subst n
          have hb : b = 0 := PrefixDigitSum_deterministic__interval_bridge _ b 0 hp (.PrefixDigitSum_nonpositive _ (by decide))
          subst b
          exact ⟨0,0,.PrefixDigitSum_nonpositive _ (by decide),.Base10DigitSum_zero,rfl⟩
        · exact PrefixDigitSum_predecessor n b (by omega) hp
      obtain ⟨pb, ps, hpb, hps, hb⟩ := hprev
      have hdecade := ih 10 ps pb 45 (by decide) (by decide) hps hpb
      have he : Z.modulo (10*b+45*((n : Int)+1)) digit_sum_modulus =
          Z.modulo (10*pb+45*(n : Int)+10*ps+45) digit_sum_modulus := by
        rw [hb, mod_scaled_add 10 (pb+ps) (45*((n : Int)+1)) digit_sum_modulus (by decide)]
        congr 1
        grind
      have hstart : PrefixDigitSum (10*((n : Int)+1)-1)
          (Z.modulo (10*b+45*((n : Int)+1)) digit_sum_modulus) := by
        rw [he]
        simpa only [show 10*((n : Int)+1)-1 = 10*(n : Int)+10-1 by omega] using hdecade
      have happ := PrefixDigitSum_append_decimal_digits ((n : Int)+1) c s _ t (by omega) hc ht hs hstart
      have hmod : Z.modulo (Z.modulo (10*b+45*((n : Int)+1)) digit_sum_modulus+c*s+t) digit_sum_modulus =
          Z.modulo (10*b+45*((n : Int)+1)+c*s+t) digit_sum_modulus := by
        unfold Z.modulo
        rw [Int.add_assoc, Int.fmod_add_fmod, ← Int.add_assoc]
      rw [hmod] at happ
      exact happ
  have hhn : (high.toNat : Int) = high := by omega
  simpa only [hhn] using hgen high.toNat count high_sum before triangle hc ht (by simpa only [hhn] using hs) (by simpa only [hhn] using hp)

theorem outer_progress_predecessor__prefix_inner_outer_scan
    (x : Int) (dp digits : List Int) (power answer_before ans j m i : Int)
    (hjdone : j ≥ Znth i digits 0) (hx : 1 ≤ x) (hi : 1 ≤ i) (him : i ≤ m) (hm : m ≤ 19)
    (hd : 0 ≤ Znth i digits 0 ∧ Znth i digits 0 < 10) (hj0 : 0 ≤ j) (hjle : j ≤ Znth i digits 0)
    (ha : 0 ≤ ans ∧ ans < 1000000007) (hb : ExtractedDigitBuffer x digits m 0)
    (hc : ExtractedDigitCount x m) (hn : InnerCandidateDigitProgressLegacy x dp digits i j answer_before ans)
    (hp : OuterDigitPositionPower i power) :
    OuterDigitPositionProgress x dp digits (i-1)
      (signed_last_nbits (Z.rem (ans+Z.rem (Z.rem (Z.rem x power+1) 1000000007 *
        Z.rem (Z.quot x power) 10) 1000000007) 1000000007) 32) := by
  have hj : j = Znth i digits 0 := by omega
  obtain ⟨_, _, hout, choice, hchoice, hans⟩ := hn
  have he : power = Z.pow 10 (i-1) := by
    rcases hp with ⟨hz,_⟩ | ⟨_,he⟩
    · omega
    · exact he
  subst power
  have hpow := pow10_pos (i-1) (by omega)
  have hmod0 : 0 ≤ Z.modulo x (Z.pow 10 (i-1)) := Int.fmod_nonneg_of_pos _ hpow
  have hdiv0 : 0 ≤ Z.div x (Z.pow 10 (i-1)) := Int.fdiv_nonneg (by omega) (by omega)
  have hquot : Z.quot x (Z.pow 10 (i-1)) = Z.div x (Z.pow 10 (i-1)) :=
    (Int.fdiv_eq_tdiv_of_nonneg (by omega) (by omega)).symm
  have hdigits := hb.2.2.2.1 i (by omega)
  rw [rem_eq_mod x _ (by omega) hpow, hquot, rem_eq_mod _ 10 hdiv0 (by decide),
    rem_eq_mod (Z.modulo x (Z.pow 10 (i-1))+1) 1000000007 (by omega) (by decide), ← hdigits]
  have hlow := mod_bounds (Z.modulo x (Z.pow 10 (i-1))+1)
  have hprod : 0 ≤ Z.modulo (Z.modulo x (Z.pow 10 (i-1))+1) 1000000007 * Znth i digits 0 :=
    Int.mul_nonneg hlow.1 hd.1
  rw [rem_eq_mod _ 1000000007 hprod (by decide)]
  have hmprod := mod_bounds (Z.modulo (Z.modulo x (Z.pow 10 (i-1))+1) 1000000007 * Znth i digits 0)
  unfold digit_sum_modulus at hmprod
  rw [rem_eq_mod _ 1000000007 (by omega) (by decide)]
  have houtmod := mod_bounds (ans+Z.modulo (Z.modulo (Z.modulo x (Z.pow 10 (i-1))+1) 1000000007 * Znth i digits 0) 1000000007)
  rw [signed_last_nbits_eq _ 32 (by decide) (by
    change -2147483648 ≤ _ ∧ _ < 2147483648
    unfold digit_sum_modulus at houtmod
    omega)]
  rw [hans]
  change DigitPositionAccumulation x dp digits (i-1) _
  have hemod : Z.modulo (Z.modulo (answer_before+choice) digit_sum_modulus +
      Z.modulo (Z.modulo (Z.modulo x (Z.pow 10 (i-1))+1) digit_sum_modulus * Znth i digits 0) digit_sum_modulus) digit_sum_modulus =
    Z.modulo (answer_before+choice+Z.modulo (Z.modulo x (Z.pow 10 (i-1))+1) digit_sum_modulus * Znth i digits 0) digit_sum_modulus := by
    unfold Z.modulo
    rw [Int.fmod_add_fmod, Int.add_fmod_fmod]
  simp only [digit_sum_modulus] at hemod ⊢
  rw [hemod]
  exact DigitPositionAccumulation_step x dp digits i answer_before choice hi hout (hj ▸ hchoice)

theorem AccumulatedDigitSumCorrect_step (x : Int) (dp digits : List Int) (count position answer choice_sum : Int)
    (hx : 1 ≤ x) (hp : 1 ≤ position ∧ position ≤ count) (hc : count ≤ 19)
    (hb : ExtractedDigitBuffer x digits count 0) (ht : DigitDPTable dp)
    (hchoice : InnerCandidateDigitSum dp position (Znth position digits 0) choice_sum)
    (hcorrect : AccumulatedDigitSumCorrect x position answer) :
    AccumulatedDigitSumCorrect x (position-1)
      (Z.modulo (answer+choice_sum+Z.modulo (Z.modulo x (Z.pow 10 (position-1))+1) digit_sum_modulus * Znth position digits 0) digit_sum_modulus) := by
  let digit := Znth position digits 0
  have hdigits : digit = Z.modulo (Z.div x (Z.pow 10 (position-1))) 10 := hb.2.2.2.1 position (by omega)
  have hdigit : 0 ≤ digit ∧ digit < 10 := by
    rw [hdigits]
    exact ⟨Int.fmod_nonneg_of_pos _ (by decide), Int.fmod_lt_of_pos _ (by decide)⟩
  have hpowpos := pow10_pos (position-1) (by omega)
  have hpower : Z.pow 10 position = Z.pow 10 (position-1)*10 := by
    simpa only [Int.sub_add_cancel] using pow_step 10 (position-1) (by omega)
  rcases hcorrect with ⟨hz,_⟩ | ⟨_, high, high_sum, before, hhigh, hhighsum, hbefore, hanswer⟩
  · omega
  have hhigh0 : 0 ≤ high := by
    rw [hhigh]
    exact Int.fdiv_nonneg (by omega) (Int.le_of_lt (pow10_pos position (by omega)))
  have hdivided : Z.div (Z.div x (Z.pow 10 (position-1))) 10 = high := by
    rw [hhigh, hpower]
    unfold Z.div
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 10),
      Int.fdiv_eq_ediv_of_nonneg _ (by omega),
      Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
    exact Int.ediv_ediv (by omega)
  have hnext : Z.div x (Z.pow 10 (position-1)) = 10*high+digit := by
    have he := Int.fmod_add_mul_fdiv (Z.div x (Z.pow 10 (position-1))) 10
    change Z.modulo (Z.div x (Z.pow 10 (position-1))) 10 + 10*Z.div (Z.div x (Z.pow 10 (position-1))) 10 = _ at he
    rw [hdivided, ← hdigits] at he
    omega
  have hrem : Z.modulo x (Z.pow 10 position) = digit*Z.pow 10 (position-1) + Z.modulo x (Z.pow 10 (position-1)) := by
    have ha := Int.fmod_add_mul_fdiv x (Z.pow 10 position)
    have hb := Int.fmod_add_mul_fdiv x (Z.pow 10 (position-1))
    change Z.modulo x (Z.pow 10 position)+Z.pow 10 position*Z.div x (Z.pow 10 position)=x at ha
    change Z.modulo x (Z.pow 10 (position-1))+Z.pow 10 (position-1)*Z.div x (Z.pow 10 (position-1))=x at hb
    rw [← hhigh, hpower] at ha
    rw [hnext] at hb
    grind
  have htriangle : ∃ triangle : Int, 2*triangle=digit*(digit-1) := by
    have hcases : digit=0 ∨ digit=1 ∨ digit=2 ∨ digit=3 ∨ digit=4 ∨ digit=5 ∨ digit=6 ∨ digit=7 ∨ digit=8 ∨ digit=9 := by omega
    rcases hcases with h|h|h|h|h|h|h|h|h|h
    · exact ⟨0,by rw [h]; decide⟩
    · exact ⟨0,by rw [h]; decide⟩
    · exact ⟨1,by rw [h]; decide⟩
    · exact ⟨3,by rw [h]; decide⟩
    · exact ⟨6,by rw [h]; decide⟩
    · exact ⟨10,by rw [h]; decide⟩
    · exact ⟨15,by rw [h]; decide⟩
    · exact ⟨21,by rw [h]; decide⟩
    · exact ⟨28,by rw [h]; decide⟩
    · exact ⟨36,by rw [h]; decide⟩
  obtain ⟨triangle, htriangle⟩ := htriangle
  have hnextsum := Base10DigitSum_append_digit high digit high_sum hhigh0 hdigit hhighsum
  change InnerCandidateDigitSum dp position digit choice_sum at hchoice
  change AccumulatedDigitSumCorrect x (position-1)
    (Z.modulo (answer+choice_sum+Z.modulo (Z.modulo x (Z.pow 10 (position-1))+1) digit_sum_modulus * digit) digit_sum_modulus)
  by_cases hlast : position=1
  · subst position
    have hcf := InnerCandidateDigitSum_one_formula dp digit choice_sum triangle hdigit htriangle ht hchoice
    have hp0 : Z.pow 10 (1-1)=1 := rfl
    have hp1 : Z.pow 10 1=10 := rfl
    have hxdec : x=10*high+digit := by simpa only [hp0, Z.div, Int.fdiv_one] using hnext
    have hxmod : Z.modulo x 10=digit := by simpa only [hp0, hp1, Z.modulo, Int.fmod_one, Int.mul_one, Int.add_zero] using hrem
    have hprefix := PrefixDigitSum_decimal_block high (digit+1) high_sum before (triangle+digit)
      hhigh0 (by omega) (by grind) hhighsum hbefore
    have hindex : 10*high+(digit+1)-1=x := by omega
    rw [hindex] at hprefix
    refine Or.inl ⟨by decide, ?_⟩
    have he : Z.modulo (answer+choice_sum+Z.modulo (Z.modulo x (Z.pow 10 (1-1))+1) digit_sum_modulus*digit) digit_sum_modulus =
        Z.modulo (10*before+45*high+(digit+1)*high_sum+(triangle+digit)) digit_sum_modulus := by
      rw [hanswer, hcf, hp0, hp1, hxmod, mod_program_update _ _ _ _ _ (by decide)]
      simp only [Z.modulo, Int.fmod_one]
      congr 1
      grind
    rw [he]
    exact hprefix
  · have hp2 : 2 ≤ position := by omega
    have hcf := InnerCandidateDigitSum_formula_ge2__digits_dp_row dp position digit choice_sum hp2
      (fun candidate hd => ht.2.2 position candidate (by omega) (by omega)) hchoice
    have hnextbefore := PrefixDigitSum_decimal_block high digit high_sum before triangle hhigh0 (by omega) htriangle hhighsum hbefore
    have hprevious : Z.pow 10 (position-1)=10*Z.pow 10 (position-2) := by
      rw [show position-1 = position-2+1 by omega, pow_step 10 (position-2) (by omega)]
      exact Int.mul_comm _ _
    refine Or.inr ⟨by omega, 10*high+digit, high_sum+digit,
      Z.modulo (10*before+45*high+digit*high_sum+triangle) digit_sum_modulus,
      hnext.symm, hnextsum, hnextbefore, ?_⟩
    rw [hanswer, hcf, mod_program_update _ _ _ _ _ (by decide)]
    have hscaled := mod_scaled_add (Z.pow 10 (position-1))
      (10*before+45*high+digit*high_sum+triangle)
      (45*(10*high+digit)*(position-1)*Z.pow 10 (position-1-1)+
        (Z.modulo x (Z.pow 10 (position-1))+1)*(high_sum+digit)) digit_sum_modulus (by decide)
    rw [← Int.add_assoc] at hscaled
    rw [hscaled, hrem, hpower, hprevious, show position-1-1 = position-2 by omega]
    congr 1
    grind

end SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_lib

namespace SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework
export annoying_math_homework_lib (digit_sum_modulus Base10DigitSum PrefixDigitSum InclusiveDigitSum IntervalDigitSum PowerTable PowerPrefix DigitDPValue DigitDPTable ZeroSegment DigitDPBaseProgress DigitDPOuterProgress DigitDPRowProgress InnerCandidateDigitSum DigitDPCellProgress ExtractedDigitBuffer ExtractedDigitCount DigitPositionPower OuterDigitPositionPower AccumulatedDigitSumCorrect DigitPositionAccumulation OuterDigitPositionProgress InnerCandidateDigitProgressLegacy CompletedDigitPositionScan)
end SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_lib
open AUXLib

def InnerCandidateDigitProgress (dp : List Int)
    (places next_digit answer_before answer : Int) : Prop :=
  ∃ choice_sum, InnerCandidateDigitSum dp places next_digit choice_sum ∧
    answer = Z.modulo (answer_before + choice_sum) digit_sum_modulus

theorem InnerCandidateDigitProgressLegacy.toAnnotation
    (h : InnerCandidateDigitProgressLegacy x dp digits places next_digit before answer) :
    InnerCandidateDigitProgress dp places next_digit before answer := h.2.2.2

end SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_lib
namespace SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework
export annoying_math_homework_lib (InnerCandidateDigitProgress)
end SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework
