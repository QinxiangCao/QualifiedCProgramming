import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.Sorting
import ListLib.General.Length

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib
open AUXLib
export AUXLib.Sorting (increasing increasing_aux lowerbound)
abbrev Some {A : Type u} (x : A) : Option A := some x
abbrev None {A : Type u} : Option A := none
abbrev _App_option_Z := Option Int

def RadixDigit (value exponent : Int) : Int := Z.modulo (Z.div value exponent) 10

def PrefixMaximum (values : List Int) (hi maximum : Int) : Prop :=
  (∃ index, (0 ≤ index ∧ index < hi) ∧ maximum = Znth index values 0) ∧
  ∀ index, (0 ≤ index ∧ index < hi) → Znth index values 0 ≤ maximum

def DecimalExponent (exponent : Int) : Prop :=
  ∃ power : Int, (0 ≤ power ∧ power ≤ 9) ∧ exponent = Z.pow 10 power

def RadixLowerDigitsOrdered (values : List Int) (exponent : Int) : Prop :=
  ∀ left right, (0 ≤ left ∧ left ≤ right ∧ right < Zlength values) →
    Z.modulo (Znth left values 0) exponent ≤ Z.modulo (Znth right values 0) exponent

def RadixPassState (input current : List Int) (exponent : Int) : Prop :=
  Permutation input current ∧ RadixLowerDigitsOrdered current exponent

def RadixBucket (values : List Int) (exponent digit : Int) : List Int :=
  values.filter (fun value => decide (RadixDigit value exponent = digit))

def RadixDigitCount (values : List Int) (exponent hi digit : Int) : Int :=
  Zlength (RadixBucket (sublist 0 hi values) exponent digit)

def DigitHistogramPrefix (values : List Int) (exponent hi : Int) (counts : List Int) : Prop :=
  ∀ digit, (0 ≤ digit ∧ digit < 10) → Znth digit counts 0 = RadixDigitCount values exponent hi digit

def DigitPrefixTotals (histogram totals : List Int) (processed : Int) : Prop :=
  ∀ digit, (0 ≤ digit ∧ digit < 10) →
    (digit < processed → Znth digit totals 0 = sum (sublist 0 (digit + 1) histogram)) ∧
    (processed ≤ digit → Znth digit totals 0 = Znth digit histogram 0)

def RadixBucketStart (histogram : List Int) (digit : Int) : Int := sum (sublist 0 digit histogram)
def RadixBucketEnd (histogram : List Int) (digit : Int) : Int := sum (sublist 0 (digit + 1) histogram)

def RadixStableOutput (source : List Int) (exponent : Int) : List Int :=
  ([0,1,2,3,4,5,6,7,8,9].map (fun digit => RadixBucket source exponent digit)).flatten

def StableDigitPass (source output : List Int) (exponent : Int) : Prop := output = RadixStableOutput source exponent

def BucketPlacementProgress (source : List Int) (exponent remaining : Int) (histogram counters : List Int)
    (mixed_output : List (Option Int)) : Prop :=
  Zlength mixed_output = 1000 ∧
  (∀ digit, (0 ≤ digit ∧ digit < 10) → Znth digit counters 0 = RadixBucketStart histogram digit + RadixDigitCount source exponent remaining digit) ∧
  (∀ digit, (0 ≤ digit ∧ digit < 10) → RadixBucketStart histogram digit ≤ Znth digit counters 0 ∧ Znth digit counters 0 ≤ RadixBucketEnd histogram digit) ∧
  (∀ digit position, (0 ≤ digit ∧ digit < 10) → (Znth digit counters 0 ≤ position ∧ position < RadixBucketEnd histogram digit) →
    Znth position mixed_output none = some (Znth position (RadixStableOutput source exponent) 0)) ∧
  (∀ position, (0 ≤ position ∧ position < 1000) →
    (∀ digit, (0 ≤ digit ∧ digit < 10) → position < Znth digit counters 0 ∨ RadixBucketEnd histogram digit ≤ position) →
    Znth position mixed_output none = none)

def RadixCopyPrefix (source pass_output working : List Int) (copied : Int) : Prop :=
  (∀ index, (0 ≤ index ∧ index < copied) → Znth index working 0 = Znth index pass_output 0) ∧
  (∀ index, (copied ≤ index ∧ index < Zlength source) → Znth index working 0 = Znth index source 0)

private theorem digit_range (value exponent : Int) : 0 ≤ RadixDigit value exponent ∧ RadixDigit value exponent < 10 :=
  ⟨Int.fmod_nonneg_of_pos _ (by decide), Int.fmod_lt_of_pos _ (by decide)⟩

private theorem ten_cases (n : Int) (h : 0 ≤ n ∧ n < 10) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega

theorem prefix_maximum_extend_greater__maximum_pass_entry (values : List Int) (hi maximum : Int)
    (hi0 : 0 ≤ hi) (h : PrefixMaximum values hi maximum) (hg : maximum < Znth hi values 0) :
    PrefixMaximum values (hi + 1) (Znth hi values 0) := by
  refine ⟨⟨hi, by omega, rfl⟩, ?_⟩
  intro index hb
  by_cases he : index = hi
  · subst index; omega
  · have := h.2 index (by omega); omega

theorem prefix_maximum_extend_bounded__maximum_pass_entry (values : List Int) (hi maximum : Int)
    (h : PrefixMaximum values hi maximum) (hb : Znth hi values 0 ≤ maximum) :
    PrefixMaximum values (hi + 1) maximum := by
  obtain ⟨⟨idx, hr, he⟩, hu⟩ := h
  refine ⟨⟨idx, by omega, he⟩, ?_⟩
  intro index hindex
  by_cases hi : index = hi
  · subst index; exact hb
  · exact hu index (by omega)

theorem decimal_exponent_active_bound__maximum_pass_entry (exponent maximum : Int)
    (he : DecimalExponent exponent) (hm : 0 ≤ maximum) (hb : maximum ≤ 999999999)
    (hq : Z.quot maximum exponent > 0) : exponent ≤ 100000000 := by
  obtain ⟨power, hp, rfl⟩ := he
  obtain h | h | h | h | h | h | h | h | h | h := ten_cases power (by omega) <;> subst power
  all_goals first | decide | (change Z.quot maximum 1000000000 > 0 at hq; have hlt := Z.quot_lt_upper_bound maximum 1000000000 1 hm (by omega) (by omega); omega)

theorem digit_histogram_prefix_zero__count_zero_init (values : List Int) (exponent : Int) (counts : List Int)
    (hz : ∀ digit, (0 ≤ digit ∧ digit < 10) → Znth digit counts 0 = 0) :
    DigitHistogramPrefix values exponent 0 counts := by
  intro digit hd; rw [hz digit hd]; rfl

theorem digit_histogram_prefix_step__histogram_update (values : List Int) (exponent hi : Int) (counts : List Int)
    (hi0 : 0 ≤ hi ∧ hi < Zlength values) (hlen : Zlength counts = 10)
    (hd : 0 ≤ RadixDigit (Znth hi values 0) exponent ∧ RadixDigit (Znth hi values 0) exponent < 10)
    (hh : DigitHistogramPrefix values exponent hi counts) :
    DigitHistogramPrefix values exponent (hi + 1)
      (replace_Znth (RadixDigit (Znth hi values 0) exponent) (Znth (RadixDigit (Znth hi values 0) exponent) counts 0 + 1) counts) := by
  intro digit hr
  have hs := hh digit hr
  unfold RadixDigitCount RadixBucket
  rw [sublist_split 0 (hi+1) hi values (by omega) (by omega), sublist_single 0 hi values hi0,
    List.filter_append, Zlength_app]
  by_cases he : RadixDigit (Znth hi values 0) exponent = digit
  · rw [← he, Znth_replace_Znth_Same 0 counts _ _ (by omega), hh _ hd]
    simp [RadixDigitCount, RadixBucket, Zlength]
  · rw [Znth_replace_Znth_Diff 0 counts _ digit _ (by omega) (by omega) he]
    simp only [List.filter_cons, decide_eq_false he, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
      Zlength_nil, Int.add_zero]
    exact hs

theorem digit_prefix_totals_init__prefix_totals (histogram : List Int) (hlen : Zlength histogram = 10) :
    DigitPrefixTotals histogram histogram 1 := by
  intro digit hd
  refine ⟨?_, fun _ => rfl⟩
  intro h
  have he : digit = 0 := by omega
  subst digit
  rw [sublist_single 0 0 histogram (by omega)]
  simp [sum]

theorem digit_prefix_totals_step__prefix_totals (histogram totals : List Int) (digit : Int)
    (hh : Zlength histogram = 10) (ht : Zlength totals = 10) (hd : 1 ≤ digit ∧ digit < 10)
    (hp : DigitPrefixTotals histogram totals digit) :
    DigitPrefixTotals histogram (replace_Znth digit (Znth digit totals 0 + Znth (digit-1) totals 0) totals) (digit+1) := by
  intro idx hi
  constructor
  · intro hlt
    by_cases he : idx = digit
    · subst idx
      rw [Znth_replace_Znth_Same 0 totals _ _ (by omega), (hp digit (by omega)).2 (by omega),
        (hp (digit-1) (by omega)).1 (by omega)]
      rw [sublist_split 0 (digit+1) digit histogram (by omega) (by omega), sublist_single 0 digit histogram (by omega), sum_app]
      simp only [show digit-1+1=digit by omega, sum, List.foldr_cons, List.foldr_nil, Int.add_zero]
      omega
    · rw [Znth_replace_Znth_Diff 0 totals digit idx _ (by omega) (by omega) (Ne.symm he)]
      exact (hp idx hi).1 (by omega)
  · intro hge
    rw [Znth_replace_Znth_Diff 0 totals digit idx _ (by omega) (by omega) (by omega)]
    exact (hp idx hi).2 (by omega)

theorem radix_digits_length__stable_placement : Zlength ([0,1,2,3,4,5,6,7,8,9] : List Int) = 10 := rfl

theorem radix_digit_c_bridge__stable_placement (value exponent : Int) (hv : 0 ≤ value) (he : 0 < exponent) :
    RadixDigit value exponent = Z.rem (Z.quot value exponent) 10 := by
  unfold RadixDigit Z.modulo Z.div Z.rem Z.quot
  rw [Int.fdiv_eq_tdiv_of_nonneg hv (by omega)]
  exact Int.fmod_eq_tmod_of_nonneg (Int.tdiv_nonneg hv (by omega)) (by decide)

theorem c_radix_digit_range__stable_placement (value exponent : Int) (hv : 0 ≤ value) (he : 0 < exponent) :
    0 ≤ Z.rem (Z.quot value exponent) 10 ∧ Z.rem (Z.quot value exponent) 10 < 10 := by
  rw [← radix_digit_c_bridge__stable_placement value exponent hv he]
  exact digit_range value exponent

theorem radix_digits_Znth__stable_placement (index : Int) (hi : 0 ≤ index ∧ index < 10) :
    Znth index [0,1,2,3,4,5,6,7,8,9] 0 = index := by
  obtain h | h | h | h | h | h | h | h | h | h := ten_cases index hi <;> subst index <;> rfl

theorem Znth_map_valid__stable_placement {A B : Type} (f : A → B) (values : List A)
    (default_a : A) (default_b : B) (index : Int) (hi : 0 ≤ index ∧ index < Zlength values) :
    Znth index (values.map f) default_b = f (Znth index values default_a) := by
  have hnat : index.toNat < values.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  simp only [Znth, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hnat,
    Option.map_some, Option.getD_some]

theorem sublist_map__stable_placement {A B : Type} (f : A → B) (lo hi : Int) (values : List A) :
    sublist lo hi (values.map f) = (sublist lo hi values).map f := by simp [sublist]

theorem Zlength_map__stable_placement {A B : Type} (f : A → B) (values : List A) :
    Zlength (values.map f) = Zlength values := by simp [Zlength]

theorem Znth_app_left__stable_placement {A : Type} (default : A) (left right : List A) (index : Int)
    (hi : 0 ≤ index ∧ index < Zlength left) : Znth index (left ++ right) default = Znth index left default :=
  ListLib.app_Znth1 default left right index hi

theorem Znth_app_right__stable_placement {A : Type} (default : A) (left right : List A) (index : Int)
    (hi : Zlength left ≤ index) : Znth index (left ++ right) default = Znth (index - Zlength left) right default :=
  app_Znth2 default left right index hi

theorem sum_sublist_ext__stable_placement (left right : List Int) (hi : Int)
    (hl : 0 ≤ hi ∧ hi ≤ Zlength left) (hr : hi ≤ Zlength right)
    (he : ∀ index, (0 ≤ index ∧ index < hi) → Znth index left 0 = Znth index right 0) :
    sum (sublist 0 hi left) = sum (sublist 0 hi right) := by
  congr 1
  apply (ListLib.list_eq_ext _ _ 0).mpr
  have hll := ListLib.Zlength_sublist 0 hi left (by omega) hl.2
  have hrl := ListLib.Zlength_sublist 0 hi right (by omega) hr
  change Zlength (sublist 0 hi left) = hi - 0 at hll
  change Zlength (sublist 0 hi right) = hi - 0 at hrl
  refine ⟨by change Zlength (sublist 0 hi left) = Zlength (sublist 0 hi right); omega, ?_⟩
  intro idx hb
  change 0 ≤ idx ∧ idx < Zlength (sublist 0 hi left) at hb
  change Znth idx (sublist 0 hi left) 0 = Znth idx (sublist 0 hi right) 0
  rw [Znth_sublist 0 0 idx hi left (by omega) (by omega), Znth_sublist 0 0 idx hi right (by omega) (by omega), Int.add_zero]
  exact he idx (by omega)

theorem Zlength_radix_concat__stable_placement (source : List Int) (exponent : Int) (digits : List Int) :
    Zlength ((digits.map (fun digit => RadixBucket source exponent digit)).flatten) =
      sum (digits.map (fun digit => Zlength (RadixBucket source exponent digit))) := by
  induction digits with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.flatten_cons, Zlength_app, ih, sum, List.foldr_cons]

theorem radix_output_as_concat__stable_placement (source : List Int) (exponent : Int) :
    RadixStableOutput source exponent = ([0,1,2,3,4,5,6,7,8,9].map (fun digit => RadixBucket source exponent digit)).flatten := rfl

theorem histogram_start_as_prefix_length__stable_placement (source : List Int) (exponent : Int) (histogram : List Int) (digit : Int)
    (hl : Zlength histogram = 10) (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hd : 0 ≤ digit ∧ digit ≤ 10) : RadixBucketStart histogram digit =
    Zlength (((sublist 0 digit [0,1,2,3,4,5,6,7,8,9]).map (fun bucket => RadixBucket source exponent bucket)).flatten) := by
  unfold RadixBucketStart
  rw [Zlength_radix_concat__stable_placement, ← sublist_map__stable_placement]
  apply sum_sublist_ext__stable_placement histogram _ digit (by omega)
  · simp only [Zlength_map__stable_placement, radix_digits_length__stable_placement]; omega
  · intro idx hi
    rw [Znth_map_valid__stable_placement _ _ 0 0 idx (by change 0 ≤ idx ∧ idx < 10; omega),
      radix_digits_Znth__stable_placement idx (by omega), hh idx (by omega)]
    unfold RadixDigitCount
    rw [sublist_self source (Zlength source) rfl]

theorem radix_output_split__stable_placement (source : List Int) (exponent digit : Int) (hd : 0 ≤ digit ∧ digit < 10) :
    RadixStableOutput source exponent =
      (((sublist 0 digit [0,1,2,3,4,5,6,7,8,9]).map (fun bucket => RadixBucket source exponent bucket)).flatten) ++
      (RadixBucket source exponent digit ++
      (((sublist (digit+1) 10 [0,1,2,3,4,5,6,7,8,9]).map (fun bucket => RadixBucket source exponent bucket)).flatten)) := by
  obtain h | h | h | h | h | h | h | h | h | h := ten_cases digit hd
  · subst digit
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = [] ++ ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ []))))))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  · subst digit
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ []) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  · subst digit
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ [])) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ []))))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  · subst digit
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ []))) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  · subst digit
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ [])))) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ []))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  · subst digit
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ []))))) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  · subst digit
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ [])))))) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ []))))
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  · subst digit
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ []))))))) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  · subst digit
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ [])))))))) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ []))
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  · subst digit
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ []))))))))) ++ ((RadixBucket source exponent 9) ++ [])
    simp only [List.append_assoc, List.nil_append, List.append_nil]

theorem bucket_end_start_count__stable_placement (source : List Int) (exponent : Int) (histogram : List Int) (digit : Int)
    (hl : Zlength histogram = 10) (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hd : 0 ≤ digit ∧ digit < 10) : RadixBucketEnd histogram digit =
    RadixBucketStart histogram digit + Zlength (RadixBucket source exponent digit) := by
  unfold RadixBucketEnd RadixBucketStart
  rw [sublist_split 0 (digit+1) digit histogram (by omega) (by omega), sublist_single 0 digit histogram (by omega), sum_app]
  have he := hh digit hd
  unfold RadixDigitCount at he
  rw [sublist_self source (Zlength source) rfl] at he
  simp only [sum, List.foldr_cons, List.foldr_nil, Int.add_zero]
  rw [he]

theorem stable_output_bucket_Znth__stable_placement (source : List Int) (exponent : Int) (histogram : List Int) (digit position : Int)
    (hl : Zlength histogram = 10) (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hd : 0 ≤ digit ∧ digit < 10) (hp : RadixBucketStart histogram digit ≤ position ∧ position < RadixBucketEnd histogram digit) :
    Znth position (RadixStableOutput source exponent) 0 =
      Znth (position - RadixBucketStart histogram digit) (RadixBucket source exponent digit) 0 := by
  have hs := histogram_start_as_prefix_length__stable_placement source exponent histogram digit hl hh (by omega)
  have he := bucket_end_start_count__stable_placement source exponent histogram digit hl hh hd
  rw [radix_output_split__stable_placement source exponent digit hd,
    Znth_app_right__stable_placement 0 _ _ position (by omega),
    Znth_app_left__stable_placement 0 _ _ _ (by omega), ← hs]

theorem sum_nonnegative_Znth__stable_placement (values : List Int)
    (h : ∀ index, (0 ≤ index ∧ index < Zlength values) → 0 ≤ Znth index values 0) : 0 ≤ sum values := by
  induction values with
  | nil => decide
  | cons x xs ih =>
    have hx : 0 ≤ x := h 0 (by simp only [Zlength, Int.ofNat_eq_coe, List.length_cons]; omega)
    have ht := ih (by
      intro idx hi
      have hs := h (idx+1) (by simp only [Zlength, Int.ofNat_eq_coe, List.length_cons] at *; omega)
      rw [Znth_cons 0 (idx+1) x xs (by omega), Int.add_sub_cancel] at hs
      exact hs)
    exact Int.add_nonneg hx ht

theorem histogram_sublist_sum_nonnegative__stable_placement (source : List Int) (exponent : Int) (histogram : List Int) (lo hi : Int)
    (hl : Zlength histogram = 10) (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ 10) : 0 ≤ sum (sublist lo hi histogram) := by
  apply sum_nonnegative_Znth__stable_placement
  intro idx hb
  have hs : Zlength (sublist lo hi histogram) = hi - lo := ListLib.Zlength_sublist lo hi histogram hlo (by change hi ≤ Zlength histogram; omega)
  rw [Znth_sublist 0 lo idx hi histogram (by omega) (by omega), hh (idx+lo) (by omega)]
  exact Zlength_nonneg _

theorem bucket_end_le_start__stable_placement (source : List Int) (exponent : Int) (histogram : List Int) (left right : Int)
    (hl : Zlength histogram = 10) (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hleft : 0 ≤ left ∧ left < 10) (hright : 0 ≤ right ∧ right ≤ 10) (horder : left < right) :
    RadixBucketEnd histogram left ≤ RadixBucketStart histogram right := by
  unfold RadixBucketEnd RadixBucketStart
  rw [sublist_split 0 right (left+1) histogram (by omega) (by omega), sum_app]
  have := histogram_sublist_sum_nonnegative__stable_placement source exponent histogram (left+1) right hl hh (by omega) hright.2
  omega

theorem bucket_ranges_overlap_digit_eq__stable_placement (source : List Int) (exponent : Int) (histogram : List Int)
    (first second first_pos second_pos : Int) (hl : Zlength histogram = 10)
    (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hf : 0 ≤ first ∧ first < 10) (hs : 0 ≤ second ∧ second < 10)
    (hfp : RadixBucketStart histogram first ≤ first_pos ∧ first_pos < RadixBucketEnd histogram first)
    (hsp : RadixBucketStart histogram second ≤ second_pos ∧ second_pos < RadixBucketEnd histogram second)
    (he : first_pos = second_pos) : first = second := by
  by_cases hlt : first < second
  · have := bucket_end_le_start__stable_placement source exponent histogram first second hl hh hf (by omega) hlt; omega
  · by_cases hgt : second < first
    · have := bucket_end_le_start__stable_placement source exponent histogram second first hl hh hs (by omega) hgt; omega
    · omega

theorem radix_digit_count_step__stable_placement (source : List Int) (exponent index digit : Int)
    (hi : 0 ≤ index ∧ index < Zlength source) :
    RadixDigitCount source exponent (index+1) digit = RadixDigitCount source exponent index digit +
      (if decide (RadixDigit (Znth index source 0) exponent = digit) then 1 else 0) := by
  unfold RadixDigitCount RadixBucket
  rw [sublist_split 0 (index+1) index source (by omega) (by omega), sublist_single 0 index source hi,
    List.filter_append, Zlength_app]
  by_cases he : RadixDigit (Znth index source 0) exponent = digit <;> simp [he, Zlength]

theorem radix_digit_count_prefix_le_full__stable_placement (source : List Int) (exponent remaining digit : Int)
    (hr : 0 ≤ remaining ∧ remaining ≤ Zlength source) :
    RadixDigitCount source exponent remaining digit ≤ RadixDigitCount source exponent (Zlength source) digit := by
  unfold RadixDigitCount RadixBucket
  rw [sublist_split 0 (Zlength source) remaining source (by omega) (by omega), List.filter_append, Zlength_app]
  have := Zlength_nonneg ((sublist remaining (Zlength source) source).filter (fun v => decide (RadixDigit v exponent = digit)))
  omega

theorem radix_digit_count_prefix_mono__stable_placement (source : List Int) (exponent lo hi digit : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength source) :
    RadixDigitCount source exponent lo digit ≤ RadixDigitCount source exponent hi digit := by
  unfold RadixDigitCount RadixBucket
  rw [sublist_split 0 hi lo source (by omega) (by omega), List.filter_append, Zlength_app]
  have := Zlength_nonneg ((sublist lo hi source).filter (fun v => decide (RadixDigit v exponent = digit)))
  omega

theorem radix_digit_count_contains_index__stable_placement (source : List Int) (exponent remaining index : Int)
    (hi : 0 ≤ index ∧ index < remaining) (hr : remaining ≤ Zlength source) :
    1 ≤ RadixDigitCount source exponent remaining (RadixDigit (Znth index source 0) exponent) := by
  have hs := radix_digit_count_step__stable_placement source exponent index (RadixDigit (Znth index source 0) exponent) (by omega)
  simp only [decide_true, Bool.true_eq, ↓reduceIte] at hs
  have hn : 0 ≤ RadixDigitCount source exponent index (RadixDigit (Znth index source 0) exponent) := Zlength_nonneg _
  have hm := radix_digit_count_prefix_mono__stable_placement source exponent (index+1) remaining (RadixDigit (Znth index source 0) exponent) (by omega) hr
  omega

theorem bucket_progress_counter_for_index__stable_placement (source : List Int) (exponent remaining : Int)
    (histogram counters : List Int) (mixed_output : List (Option Int)) (index : Int)
    (hl : Zlength histogram = 10) (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hp : BucketPlacementProgress source exponent remaining histogram counters mixed_output)
    (hi : 0 ≤ index ∧ index < remaining) (hr : remaining ≤ Zlength source)
    (hd : 0 ≤ RadixDigit (Znth index source 0) exponent ∧ RadixDigit (Znth index source 0) exponent < 10) :
    1 ≤ Znth (RadixDigit (Znth index source 0) exponent) counters 0 := by
  rw [hp.2.1 _ hd]
  have hc := radix_digit_count_contains_index__stable_placement source exponent remaining index hi hr
  have hs := histogram_sublist_sum_nonnegative__stable_placement source exponent histogram 0 (RadixDigit (Znth index source 0) exponent) hl hh (by omega) (by omega)
  change 0 ≤ RadixBucketStart histogram (RadixDigit (Znth index source 0) exponent) at hs
  omega

theorem radix_bucket_current_position__stable_placement (source : List Int) (exponent index digit : Int)
    (hi : 0 ≤ index ∧ index < Zlength source) (hd : digit = RadixDigit (Znth index source 0) exponent) :
    Znth (RadixDigitCount source exponent index digit) (RadixBucket source exponent digit) 0 = Znth index source 0 ∧
    RadixDigitCount source exponent index digit < RadixDigitCount source exponent (Zlength source) digit := by
  have hsplit : source = sublist 0 index source ++ ([Znth index source 0] ++ sublist (index+1) (Zlength source) source) := by
    rw [← sublist_single 0 index source hi, ← sublist_split index (Zlength source) (index+1) source (by omega) (by omega),
      ← sublist_split 0 (Zlength source) index source (by omega) (by omega), sublist_self source (Zlength source) rfl]
  have hb : RadixBucket source exponent digit = RadixBucket (sublist 0 index source) exponent digit ++
      (Znth index source 0 :: RadixBucket (sublist (index+1) (Zlength source) source) exponent digit) := by
    unfold RadixBucket
    conv => lhs; rw [hsplit]
    rw [List.filter_append, List.filter_append]
    simp [← hd]
  have hf : RadixDigitCount source exponent (Zlength source) digit = Zlength (RadixBucket source exponent digit) := by
    unfold RadixDigitCount; rw [sublist_self source (Zlength source) rfl]
  rw [hf, hb]
  change Znth (Zlength (RadixBucket (sublist 0 index source) exponent digit)) _ 0 = _ ∧
    Zlength (RadixBucket (sublist 0 index source) exponent digit) < _
  constructor
  · rw [Znth_app_right__stable_placement 0 _ _ _ (by omega), Int.sub_self]; rfl
  · rw [Zlength_app, Zlength_cons]
    have := Zlength_nonneg (RadixBucket (sublist (index+1) (Zlength source) source) exponent digit)
    omega

theorem radix_current_stable_position__stable_placement (source : List Int) (exponent : Int) (histogram : List Int) (index : Int)
    (hl : Zlength histogram = 10) (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hi : 0 ≤ index ∧ index < Zlength source)
    (hd : 0 ≤ RadixDigit (Znth index source 0) exponent ∧ RadixDigit (Znth index source 0) exponent < 10) :
    Znth (RadixBucketStart histogram (RadixDigit (Znth index source 0) exponent) +
      RadixDigitCount source exponent index (RadixDigit (Znth index source 0) exponent)) (RadixStableOutput source exponent) 0 =
      Znth index source 0 := by
  have hc := radix_bucket_current_position__stable_placement source exponent index (RadixDigit (Znth index source 0) exponent) hi rfl
  have he := bucket_end_start_count__stable_placement source exponent histogram _ hl hh hd
  have hn : 0 ≤ RadixDigitCount source exponent index (RadixDigit (Znth index source 0) exponent) := Zlength_nonneg _
  have hf : RadixDigitCount source exponent (Zlength source) (RadixDigit (Znth index source 0) exponent) =
      Zlength (RadixBucket source exponent (RadixDigit (Znth index source 0) exponent)) := by
    unfold RadixDigitCount; rw [sublist_self source (Zlength source) rfl]
  rw [stable_output_bucket_Znth__stable_placement source exponent histogram _ _ hl hh hd (by omega), show RadixBucketStart histogram (RadixDigit (Znth index source 0) exponent) + RadixDigitCount source exponent index (RadixDigit (Znth index source 0) exponent) - RadixBucketStart histogram (RadixDigit (Znth index source 0) exponent) = RadixDigitCount source exponent index (RadixDigit (Znth index source 0) exponent) by omega]
  exact hc.1

theorem bucket_placement_initial__stable_placement (source : List Int) (exponent : Int) (histogram endpoints : List Int)
    (hl : Zlength histogram = 10) (he : Zlength endpoints = 10)
    (hh : DigitHistogramPrefix source exponent (Zlength source) histogram) (ht : DigitPrefixTotals histogram endpoints 10) :
    BucketPlacementProgress source exponent (Zlength source) histogram endpoints (List.replicate (1000 : Int).toNat none) := by
  have hend : ∀ digit, (0 ≤ digit ∧ digit < 10) → Znth digit endpoints 0 = RadixBucketEnd histogram digit := by
    intro digit hd; exact (ht digit hd).1 hd.2
  have hfull : ∀ digit, RadixDigitCount source exponent (Zlength source) digit = Zlength (RadixBucket source exponent digit) := by
    intro digit; unfold RadixDigitCount; rw [sublist_self source (Zlength source) rfl]
  refine ⟨by rw [Zlength, List.length_replicate]; rfl, ?_, ?_, ?_, ?_⟩
  · intro digit hd
    rw [hend digit hd, bucket_end_start_count__stable_placement source exponent histogram digit hl hh hd, hfull digit]
  · intro digit hd
    rw [hend digit hd]
    have heq := bucket_end_start_count__stable_placement source exponent histogram digit hl hh hd
    have hn := Zlength_nonneg (RadixBucket source exponent digit)
    omega
  · intro digit pos hd hp; rw [hend digit hd] at hp; omega
  · intro pos hp hall; exact Znth_repeat none 1000 pos

theorem radix_output_cons_insertion__stable_placement (value : Int) (source : List Int) (exponent digit : Int)
    (he : digit = RadixDigit value exponent) (hd : 0 ≤ digit ∧ digit < 10) :
    ∃ before after, RadixStableOutput source exponent = before ++ after ∧
      RadixStableOutput (value :: source) exponent = before ++ (value :: after) := by
  refine ⟨((sublist 0 digit [0,1,2,3,4,5,6,7,8,9]).map (fun b => RadixBucket source exponent b)).flatten,
    RadixBucket source exponent digit ++ (((sublist (digit+1) 10 [0,1,2,3,4,5,6,7,8,9]).map (fun b => RadixBucket source exponent b)).flatten),
    radix_output_split__stable_placement source exponent digit hd, ?_⟩
  obtain h | h | h | h | h | h | h | h | h | h := ten_cases digit hd
  · rw [h] at he ⊢
    conv => lhs; unfold RadixStableOutput; simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, RadixBucket, List.filter_cons, ← he]
    change ((value :: (RadixBucket source exponent 0)) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = [] ++ (value :: ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append]
  · rw [h] at he ⊢
    conv => lhs; unfold RadixStableOutput; simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, RadixBucket, List.filter_cons, ← he]
    change ((RadixBucket source exponent 0) ++ ((value :: (RadixBucket source exponent 1)) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ []) ++ (value :: ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ []))))))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append]
  · rw [h] at he ⊢
    conv => lhs; unfold RadixStableOutput; simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, RadixBucket, List.filter_cons, ← he]
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((value :: (RadixBucket source exponent 2)) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ [])) ++ (value :: ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append]
  · rw [h] at he ⊢
    conv => lhs; unfold RadixStableOutput; simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, RadixBucket, List.filter_cons, ← he]
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((value :: (RadixBucket source exponent 3)) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ []))) ++ (value :: ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ []))))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append]
  · rw [h] at he ⊢
    conv => lhs; unfold RadixStableOutput; simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, RadixBucket, List.filter_cons, ← he]
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((value :: (RadixBucket source exponent 4)) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ [])))) ++ (value :: ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append]
  · rw [h] at he ⊢
    conv => lhs; unfold RadixStableOutput; simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, RadixBucket, List.filter_cons, ← he]
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((value :: (RadixBucket source exponent 5)) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ []))))) ++ (value :: ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ []))))))
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append]
  · rw [h] at he ⊢
    conv => lhs; unfold RadixStableOutput; simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, RadixBucket, List.filter_cons, ← he]
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((value :: (RadixBucket source exponent 6)) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ [])))))) ++ (value :: ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append]
  · rw [h] at he ⊢
    conv => lhs; unfold RadixStableOutput; simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, RadixBucket, List.filter_cons, ← he]
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((value :: (RadixBucket source exponent 7)) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ []))))))) ++ (value :: ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ []))))
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append]
  · rw [h] at he ⊢
    conv => lhs; unfold RadixStableOutput; simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, RadixBucket, List.filter_cons, ← he]
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((value :: (RadixBucket source exponent 8)) ++ ((RadixBucket source exponent 9) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ [])))))))) ++ (value :: ((RadixBucket source exponent 8) ++ ((RadixBucket source exponent 9) ++ [])))
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append]
  · rw [h] at he ⊢
    conv => lhs; unfold RadixStableOutput; simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, RadixBucket, List.filter_cons, ← he]
    change ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ ((value :: (RadixBucket source exponent 9)) ++ [])))))))))) = ((RadixBucket source exponent 0) ++ ((RadixBucket source exponent 1) ++ ((RadixBucket source exponent 2) ++ ((RadixBucket source exponent 3) ++ ((RadixBucket source exponent 4) ++ ((RadixBucket source exponent 5) ++ ((RadixBucket source exponent 6) ++ ((RadixBucket source exponent 7) ++ ((RadixBucket source exponent 8) ++ []))))))))) ++ (value :: ((RadixBucket source exponent 9) ++ []))
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append]

theorem radix_stable_output_permutation__stable_placement (source : List Int) (exponent : Int)
    (hd : ∀ index, (0 ≤ index ∧ index < Zlength source) → 0 ≤ RadixDigit (Znth index source 0) exponent ∧ RadixDigit (Znth index source 0) exponent < 10) :
    Permutation source (RadixStableOutput source exponent) := by
  induction source with
  | nil => exact List.Perm.refl []
  | cons x xs ih =>
    have ht := ih (fun index hi => digit_range _ _)
    obtain ⟨before, after, he, hn⟩ := radix_output_cons_insertion__stable_placement x xs exponent (RadixDigit x exponent) rfl (digit_range x exponent)
    rw [he] at ht
    rw [hn]
    exact (List.Perm.cons x ht).trans (List.perm_middle.symm)

private theorem nth_mem {A : Type} (l : List A) (d : A) (i : Int) (h : 0 ≤ i ∧ i < Zlength l) :
    Znth i l d ∈ l := by
  unfold Znth
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [Zlength, Int.ofNat_eq_coe] at h; omega)]
  simp only [Option.getD_some]
  exact List.getElem_mem _

private theorem mem_nth {A : Type} (l : List A) (d v : A) (h : v ∈ l) :
    ∃ i : Int, (0 ≤ i ∧ i < Zlength l) ∧ Znth i l d = v := by
  obtain ⟨i, hi, hv⟩ := List.mem_iff_getElem.mp h
  refine ⟨i, ⟨by omega, by simp only [Zlength, Int.ofNat_eq_coe]; omega⟩, ?_⟩
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using hv

theorem radix_stable_output_properties__stable_placement (source : List Int) (exponent lower upper : Int)
    (hv : ∀ index, (0 ≤ index ∧ index < Zlength source) → (lower ≤ Znth index source 0 ∧ Znth index source 0 ≤ upper) ∧
      (0 ≤ RadixDigit (Znth index source 0) exponent ∧ RadixDigit (Znth index source 0) exponent < 10)) :
    Zlength (RadixStableOutput source exponent) = Zlength source ∧ Permutation source (RadixStableOutput source exponent) ∧
    (∀ index, (0 ≤ index ∧ index < Zlength source) → lower ≤ Znth index (RadixStableOutput source exponent) 0 ∧ Znth index (RadixStableOutput source exponent) 0 ≤ upper) := by
  have hp := radix_stable_output_permutation__stable_placement source exponent (fun idx hi => (hv idx hi).2)
  have hl : Zlength (RadixStableOutput source exponent) = Zlength source := by unfold Zlength; rw [hp.length_eq]
  refine ⟨hl, hp, ?_⟩
  intro idx hi
  obtain ⟨j, hj, he⟩ := mem_nth source 0 _ (hp.mem_iff.mpr (nth_mem _ 0 idx (by omega)))
  rw [← he]
  exact (hv j hj).1

theorem radix_position_bucket__stable_placement (source : List Int) (exponent : Int) (histogram : List Int) (position : Int)
    (hl : Zlength histogram = 10) (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hd : ∀ index, (0 ≤ index ∧ index < Zlength source) → 0 ≤ RadixDigit (Znth index source 0) exponent ∧ RadixDigit (Znth index source 0) exponent < 10)
    (hp : 0 ≤ position ∧ position < Zlength source) :
    ∃ digit, (0 ≤ digit ∧ digit < 10) ∧ RadixBucketStart histogram digit ≤ position ∧ position < RadixBucketEnd histogram digit := by
  have hperm := radix_stable_output_permutation__stable_placement source exponent hd
  have hlen : Zlength (RadixStableOutput source exponent) = Zlength source := by unfold Zlength; rw [hperm.length_eq]
  have hlast := histogram_start_as_prefix_length__stable_placement source exponent histogram 10 hl hh (by decide)
  have hlast' : RadixBucketEnd histogram 9 = Zlength source := by
    change RadixBucketStart histogram 10 = Zlength source
    simpa only [sublist_self ([0,1,2,3,4,5,6,7,8,9] : List Int) 10 rfl, ← radix_output_as_concat__stable_placement, hlen] using hlast
  by_cases h0 : position < RadixBucketEnd histogram 0
  · exact ⟨0, by decide, hp.1, h0⟩
  by_cases h1 : position < RadixBucketEnd histogram 1
  · exact ⟨1, by decide, by change RadixBucketEnd histogram 0 ≤ position; omega, h1⟩
  by_cases h2 : position < RadixBucketEnd histogram 2
  · exact ⟨2, by decide, by change RadixBucketEnd histogram 1 ≤ position; omega, h2⟩
  by_cases h3 : position < RadixBucketEnd histogram 3
  · exact ⟨3, by decide, by change RadixBucketEnd histogram 2 ≤ position; omega, h3⟩
  by_cases h4 : position < RadixBucketEnd histogram 4
  · exact ⟨4, by decide, by change RadixBucketEnd histogram 3 ≤ position; omega, h4⟩
  by_cases h5 : position < RadixBucketEnd histogram 5
  · exact ⟨5, by decide, by change RadixBucketEnd histogram 4 ≤ position; omega, h5⟩
  by_cases h6 : position < RadixBucketEnd histogram 6
  · exact ⟨6, by decide, by change RadixBucketEnd histogram 5 ≤ position; omega, h6⟩
  by_cases h7 : position < RadixBucketEnd histogram 7
  · exact ⟨7, by decide, by change RadixBucketEnd histogram 6 ≤ position; omega, h7⟩
  by_cases h8 : position < RadixBucketEnd histogram 8
  · exact ⟨8, by decide, by change RadixBucketEnd histogram 7 ≤ position; omega, h8⟩
  exact ⟨9, by decide, by change RadixBucketEnd histogram 8 ≤ position; omega, by omega⟩

theorem bucket_placement_complete__stable_placement (source : List Int) (exponent : Int) (histogram counters : List Int)
    (mixed_output : List (Option Int)) (hl : Zlength histogram = 10) (hlen : Zlength source ≤ 1000)
    (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hd : ∀ index, (0 ≤ index ∧ index < Zlength source) → 0 ≤ RadixDigit (Znth index source 0) exponent ∧ RadixDigit (Znth index source 0) exponent < 10)
    (hp : BucketPlacementProgress source exponent 0 histogram counters mixed_output) :
    (∀ digit, (0 ≤ digit ∧ digit < 10) → Znth digit counters 0 = RadixBucketStart histogram digit) ∧
    sublist 0 (Zlength source) mixed_output = (RadixStableOutput source exponent).map some := by
  have hc : ∀ digit, (0 ≤ digit ∧ digit < 10) → Znth digit counters 0 = RadixBucketStart histogram digit := by
    intro digit hd; simpa [RadixDigitCount, RadixBucket, sublist, Zlength] using hp.2.1 digit hd
  refine ⟨hc, ?_⟩
  apply (ListLib.list_eq_ext _ _ none).mpr
  have hperm := radix_stable_output_permutation__stable_placement source exponent hd
  have hslen : Zlength (RadixStableOutput source exponent) = Zlength source := by unfold Zlength; rw [hperm.length_eq]
  have hm : Zlength (sublist 0 (Zlength source) mixed_output) = Zlength source := by
    have h : Zlength (sublist 0 (Zlength source) mixed_output) = Zlength source - 0 :=
      ListLib.Zlength_sublist 0 (Zlength source) mixed_output (by have := Zlength_nonneg source; omega) (by change Zlength source ≤ Zlength mixed_output; have := hp.1; omega)
    omega
  refine ⟨by change Zlength (sublist 0 (Zlength source) mixed_output) = Zlength ((RadixStableOutput source exponent).map some); rw [Zlength_map__stable_placement, hm, hslen], ?_⟩
  intro idx hi
  change 0 ≤ idx ∧ idx < Zlength (sublist 0 (Zlength source) mixed_output) at hi
  change Znth idx (sublist 0 (Zlength source) mixed_output) none = Znth idx ((RadixStableOutput source exponent).map some) none
  rw [Znth_sublist none 0 idx (Zlength source) mixed_output (by omega) (by omega), Int.add_zero,
    Znth_map_valid__stable_placement some _ 0 none idx (by omega)]
  obtain ⟨digit, hdr, hpos⟩ := radix_position_bucket__stable_placement source exponent histogram idx hl hh hd (by omega)
  exact hp.2.2.2.1 digit idx hdr (by rw [hc digit hdr]; exact hpos)

theorem radix_copy_prefix_zero__copy_back (source pass_output : List Int) : RadixCopyPrefix source pass_output source 0 := by
  refine ⟨?_, fun _ _ => rfl⟩; intro idx hi; omega

theorem radix_copy_prefix_step__copy_back (source pass_output working : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength source) (hl : Zlength working = Zlength source)
    (hp : RadixCopyPrefix source pass_output working i) :
    RadixCopyPrefix source pass_output (replace_Znth i (Znth i pass_output 0) working) (i+1) := by
  constructor
  · intro idx hb
    by_cases he : idx = i
    · subst idx; exact Znth_replace_Znth_Same 0 working i _ (by omega)
    · rw [Znth_replace_Znth_Diff 0 working i idx _ (by omega) (by omega) (Ne.symm he)]
      exact hp.1 idx (by omega)
  · intro idx hb
    rw [Znth_replace_Znth_Diff 0 working i idx _ (by omega) (by omega) (by omega)]
    exact hp.2 idx (by omega)

theorem count_occ_radix_bucket__pass_transition (source : List Int) (exponent digit value : Int) :
    (RadixBucket source exponent digit).count value =
      if decide (RadixDigit value exponent = digit) then source.count value else 0 := by
  unfold RadixBucket
  induction source with
  | nil => simp
  | cons x xs ih =>
    by_cases he : x = value
    · subst x; by_cases hd : RadixDigit value exponent = digit <;> simp [hd, ih]
    · by_cases hd : RadixDigit x exponent = digit <;> simp [hd, he, ih]

theorem stable_digit_pass_permutation__pass_transition (source output : List Int) (exponent : Int)
    (hp : StableDigitPass source output exponent) : Permutation source output := by
  rw [hp]
  exact radix_stable_output_permutation__stable_placement source exponent (fun _ _ => digit_range _ _)

-- Reached dependency: Coq.Sorting.Sorted.StronglySorted, with source constructor order.
inductive StronglySorted {A : Type} (R : A → A → Prop) : List A → Prop where
  | SSorted_nil : StronglySorted R []
  | SSorted_cons (a : A) {l : List A} : StronglySorted R l → Forall (R a) l → StronglySorted R (a :: l)

@[match_pattern] abbrev SSorted_nil {A : Type} (R : A → A → Prop) : StronglySorted R [] := .SSorted_nil
@[match_pattern] abbrev SSorted_cons {A : Type} {R : A → A → Prop} (a : A) {l : List A}
    (ht : StronglySorted R l) (hh : Forall (R a) l) : StronglySorted R (a :: l) := .SSorted_cons a ht hh

private theorem strongly_pairwise {A : Type} (R : A → A → Prop) (l : List A) : StronglySorted R l ↔ l.Pairwise R := by
  induction l with
  | nil => exact ⟨fun _ => .nil, fun _ => .SSorted_nil⟩
  | cons x xs ih =>
    constructor
    · intro h
      cases h with
      | SSorted_cons _ ht hh => exact .cons (fun y hy => Forall.mem hh hy) (ih.mp ht)
    · intro h
      obtain ⟨hh, ht⟩ := List.pairwise_cons.mp h
      exact .SSorted_cons x (ih.mpr ht) (Forall.iff_forall_mem.mpr hh)

theorem forall_znth__pass_transition {A : Type} (P : A → Prop) (default : A) (values : List A) :
    Forall P values ↔ ∀ index, (0 ≤ index ∧ index < Zlength values) → P (Znth index values default) := by
  rw [Forall.iff_forall_mem]
  constructor
  · intro h idx hi; exact h _ (nth_mem values default idx hi)
  · intro h x hx
    obtain ⟨idx, hi, he⟩ := mem_nth values default x hx
    rw [← he]; exact h idx hi

theorem strongly_sorted_cons_iff__pass_transition (R : Int → Int → Prop) (head : Int) (tail : List Int) :
    StronglySorted R (head :: tail) ↔ Forall (R head) tail ∧ StronglySorted R tail := by
  constructor
  · intro h; cases h with | SSorted_cons _ ht hh => exact ⟨hh, ht⟩
  · intro h; exact .SSorted_cons head h.2 h.1

theorem strongly_sorted_iff_index__pass_transition (R : Int → Int → Prop) (values : List Int) :
    StronglySorted R values ↔ ∀ left right, 0 ≤ left → left < right → right < Zlength values → R (Znth left values 0) (Znth right values 0) := by
  induction values with
  | nil => constructor <;> intro h; intro l r hl ho hr; have : Zlength ([] : List Int) = 0 := rfl; omega; exact .SSorted_nil
  | cons x xs ih =>
    rw [strongly_sorted_cons_iff__pass_transition, forall_znth__pass_transition (R x) 0 xs, ih]
    constructor
    · intro ⟨hh, ht⟩ l r hl ho hr
      by_cases he : l = 0
      · subst l
        rw [Znth0_cons, Znth_cons 0 r x xs (by omega)]
        exact hh (r-1) (by simp only [Zlength, Int.ofNat_eq_coe, List.length_cons] at *; omega)
      · rw [Znth_cons 0 l x xs (by omega), Znth_cons 0 r x xs (by omega)]
        exact ht (l-1) (r-1) (by omega) (by omega) (by simp only [Zlength, Int.ofNat_eq_coe, List.length_cons] at *; omega)
    · intro h
      constructor
      · intro idx hi
        have hs := h 0 (idx+1) (by omega) (by omega) (by simp only [Zlength, Int.ofNat_eq_coe, List.length_cons] at *; omega)
        simpa only [Znth0_cons, Znth_cons 0 (idx+1) x xs (by omega), Int.add_sub_cancel] using hs
      · intro l r hl ho hr
        have hs := h (l+1) (r+1) (by omega) (by omega) (by simp only [Zlength, Int.ofNat_eq_coe, List.length_cons] at *; omega)
        simpa only [Znth_cons 0 (l+1) x xs (by omega), Znth_cons 0 (r+1) x xs (by omega), Int.add_sub_cancel] using hs

theorem strongly_sorted_app__pass_transition (R : Int → Int → Prop) (left_values right_values : List Int) :
    StronglySorted R (left_values ++ right_values) ↔
    StronglySorted R left_values ∧ StronglySorted R right_values ∧
    (∀ left right, In left left_values → In right right_values → R left right) := by
  rw [strongly_pairwise, List.pairwise_append, ← strongly_pairwise, ← strongly_pairwise]
  constructor
  · intro ⟨hl, hr, hc⟩; exact ⟨hl, hr, fun l r hl hr => hc l hl r hr⟩
  · intro ⟨hl, hr, hc⟩; exact ⟨hl, hr, fun l hl r hr => hc l r hl hr⟩

theorem strongly_sorted_filter__pass_transition (R : Int → Int → Prop) (test : Int → Bool) (values : List Int)
    (h : StronglySorted R values) : StronglySorted R (values.filter test) :=
  (strongly_pairwise _ _).mpr ((strongly_pairwise _ _).mp h |>.filter test)

theorem strongly_sorted_weaken__pass_transition (R S : Int → Int → Prop) (values : List Int)
    (h : StronglySorted R values) (hw : ∀ left right, In left values → In right values → R left right → S left right) :
    StronglySorted S values :=
  (strongly_pairwise _ _).mpr (((strongly_pairwise _ _).mp h).imp_of_mem (fun hl hr hrel => hw _ _ hl hr hrel))

theorem radix_mod_decompose__pass_transition (value exponent : Int) (he : 0 < exponent) :
    Z.modulo value (exponent*10) = RadixDigit value exponent * exponent + Z.modulo value exponent := by
  simpa only [Int.mul_comm exponent 10] using Z.mod_recombine value 10 exponent (by decide) he

theorem radix_bucket_chain__pass_transition (source : List Int) (exponent digit : Int) (he : 0 < exponent)
    (hs : StronglySorted (fun l r => Z.modulo l exponent ≤ Z.modulo r exponent) source) :
    StronglySorted (fun l r => Z.modulo l (exponent*10) ≤ Z.modulo r (exponent*10)) (RadixBucket source exponent digit) := by
  apply strongly_sorted_weaken__pass_transition _ _ _ (strongly_sorted_filter__pass_transition _ _ _ hs)
  intro l r hl hr hrel
  have hld : RadixDigit l exponent = digit := of_decide_eq_true (List.mem_filter.mp hl).2
  have hrd : RadixDigit r exponent = digit := of_decide_eq_true (List.mem_filter.mp hr).2
  rw [radix_mod_decompose__pass_transition l exponent he, radix_mod_decompose__pass_transition r exponent he, hld, hrd]
  omega

theorem radix_bucket_cross__pass_transition (source : List Int) (exponent left_digit right_digit left right : Int)
    (he : 0 < exponent) (hd : left_digit < right_digit)
    (hl : In left (RadixBucket source exponent left_digit)) (hr : In right (RadixBucket source exponent right_digit)) :
    Z.modulo left (exponent*10) ≤ Z.modulo right (exponent*10) := by
  have hld : RadixDigit left exponent = left_digit := of_decide_eq_true (List.mem_filter.mp hl).2
  have hrd : RadixDigit right exponent = right_digit := of_decide_eq_true (List.mem_filter.mp hr).2
  have hlmod : 0 ≤ Z.modulo left exponent ∧ Z.modulo left exponent < exponent :=
    ⟨Int.fmod_nonneg_of_pos _ he, Int.fmod_lt_of_pos _ he⟩
  have hrmod : 0 ≤ Z.modulo right exponent ∧ Z.modulo right exponent < exponent :=
    ⟨Int.fmod_nonneg_of_pos _ he, Int.fmod_lt_of_pos _ he⟩
  have hm := Int.mul_le_mul_of_nonneg_right (show left_digit+1 ≤ right_digit by omega) (show 0 ≤ exponent by omega)
  rw [radix_mod_decompose__pass_transition left exponent he, radix_mod_decompose__pass_transition right exponent he, hld, hrd]
  simp only [Int.add_mul, Int.one_mul] at hm
  omega

theorem radix_buckets_chain__pass_transition (digits source : List Int) (exponent : Int) (he : 0 < exponent)
    (hs : StronglySorted (fun l r => Z.modulo l exponent ≤ Z.modulo r exponent) source)
    (hd : StronglySorted (· < ·) digits) :
    StronglySorted (fun l r => Z.modulo l (exponent*10) ≤ Z.modulo r (exponent*10))
      ((digits.map (fun digit => RadixBucket source exponent digit)).flatten) := by
  induction hd with
  | SSorted_nil => exact .SSorted_nil
  | @SSorted_cons digit digits htail hlater ih =>
    apply (strongly_sorted_app__pass_transition _ _ _).mpr
    refine ⟨radix_bucket_chain__pass_transition source exponent digit he hs, ih, ?_⟩
    intro l r hl hr
    obtain ⟨bucket, hb, hr⟩ := List.mem_flatten.mp hr
    obtain ⟨rd, hrd, rfl⟩ := List.mem_map.mp hb
    exact radix_bucket_cross__pass_transition source exponent digit rd l r he (Forall.mem hlater hrd) hl hr

theorem stable_digit_pass_next_order__pass_transition (source output : List Int) (exponent : Int)
    (he : 0 < exponent) (ho : RadixLowerDigitsOrdered source exponent) (hp : StableDigitPass source output exponent) :
    RadixLowerDigitsOrdered output (exponent*10) := by
  rw [hp]
  have hs := (strongly_sorted_iff_index__pass_transition (fun l r => Z.modulo l exponent ≤ Z.modulo r exponent) source).mpr (fun l r hl hlr hr => ho l r (by omega))
  have hd : StronglySorted (fun l r : Int => l < r) [0,1,2,3,4,5,6,7,8,9] := by
    apply (strongly_pairwise _ _).mpr
    decide
  have hout := radix_buckets_chain__pass_transition [0,1,2,3,4,5,6,7,8,9] source exponent he hs hd
  intro l r hb
  by_cases heq : l = r
  · subst l; exact Int.le_refl _
  · exact (strongly_sorted_iff_index__pass_transition _ _).mp hout l r hb.1 (by omega) hb.2.2

theorem decimal_exponent_next__pass_transition (exponent : Int) (he : DecimalExponent exponent) (hb : exponent ≤ 100000000) :
    DecimalExponent (exponent*10) := by
  obtain ⟨power, hp, rfl⟩ := he
  obtain h | h | h | h | h | h | h | h | h | h := ten_cases power (by omega) <;> subst power
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩
  · exact ⟨8, by decide, rfl⟩
  · exact ⟨9, by decide, rfl⟩
  · change (1000000000 : Int) ≤ 100000000 at hb; omega

-- Reached recursive dependency from Rocq/auxlibs/ListLib.v.
def upperbound (maximum : Int) : List Int → Prop
  | [] => True
  | x :: xs => x ≤ maximum ∧ upperbound maximum xs

private theorem upperbound_iff (maximum : Int) (values : List Int) :
    upperbound maximum values ↔ ∀ value, value ∈ values → value ≤ maximum := by
  induction values with
  | nil => simp only [upperbound, List.not_mem_nil, false_implies, implies_true]
  | cons x xs ih => simp only [upperbound, ih, List.mem_cons, forall_eq_or_imp]

theorem upperbound_permutation__final_result (maximum : Int) (left right : List Int)
    (hp : Permutation left right) (hu : upperbound maximum left) : upperbound maximum right := by
  rw [upperbound_iff] at hu ⊢
  intro v hv
  exact hu v (hp.mem_iff.mpr hv)

private theorem pairwise_increasing (values : List Int) (h : values.Pairwise (· ≤ ·)) : increasing values := by
  induction values with
  | nil => trivial
  | cons x xs ih =>
    cases xs with
    | nil => trivial
    | cons y ys =>
      exact ⟨(List.pairwise_cons.mp h).1 y (List.mem_cons_self), ih (List.pairwise_cons.mp h).2⟩

theorem radix_lower_order_increasing__final_result (values : List Int) (exponent maximum : Int)
    (he : 0 < exponent) (hm : maximum < exponent) (hl : lowerbound 0 values) (hu : upperbound maximum values)
    (ho : RadixLowerDigitsOrdered values exponent) : increasing values := by
  apply pairwise_increasing
  apply (strongly_pairwise _ _).mp
  apply (strongly_sorted_iff_index__pass_transition _ _).mpr
  intro l r hleft horder hright
  have hlm := nth_mem values 0 l (by omega)
  have hrm := nth_mem values 0 r (by omega)
  have hln := (AUXLib.Sorting.lowerbound_iff _ _).mp hl _ hlm
  have hrn := (AUXLib.Sorting.lowerbound_iff _ _).mp hl _ hrm
  have hlu := (upperbound_iff _ _).mp hu _ hlm
  have hru := (upperbound_iff _ _).mp hu _ hrm
  have hrel := ho l r (by omega)
  unfold Z.modulo at hrel
  rw [Int.fmod_eq_of_lt hln (by omega), Int.fmod_eq_of_lt hrn (by omega)] at hrel
  exact hrel

theorem radix_pass_state_final_increasing__final_result (input current : List Int) (n exponent maximum : Int)
    (hli : Zlength input = n) (hlc : Zlength current = n) (he : 0 < exponent) (hm : 0 ≤ maximum)
    (hq : Z.quot maximum exponent ≤ 0) (hcn : ∀ index, (0 ≤ index ∧ index < n) → 0 ≤ Znth index current 0)
    (hp : PrefixMaximum input n maximum) (hs : RadixPassState input current exponent) : increasing current := by
  have hlt : maximum < exponent := by
    by_cases hlt : maximum < exponent
    · exact hlt
    · have := Z.quot_le_lower_bound maximum exponent 1 he (by omega); omega
  have hu : upperbound maximum input := by
    rw [upperbound_iff]
    intro v hv
    obtain ⟨idx, hi, heq⟩ := mem_nth input 0 v hv
    rw [← heq]
    exact hp.2 idx (by omega)
  apply radix_lower_order_increasing__final_result current exponent maximum he hlt
  · rw [AUXLib.Sorting.lowerbound_iff]
    intro v hv
    obtain ⟨idx, hi, heq⟩ := mem_nth current 0 v hv
    rw [← heq]
    exact hcn idx (by omega)
  · exact upperbound_permutation__final_result maximum input current hs.1 hu
  · exact hs.2

theorem increasing_short_list__final_result (values : List Int) (hl : Zlength values ≤ 1) : increasing values := by
  cases values with
  | nil => trivial
  | cons x xs =>
    cases xs with
    | nil => trivial
    | cons y ys => simp only [Zlength, Int.ofNat_eq_coe, List.length_cons] at hl; omega

theorem digit_histogram_prefix_mass_bound__prefix_totals (values : List Int) (exponent hi : Int) (histogram : List Int) (digit : Int)
    (hi0 : 0 ≤ hi ∧ hi ≤ Zlength values) (hhlen : Zlength histogram = 10)
    (hh : DigitHistogramPrefix values exponent hi histogram) (hd : 0 ≤ digit ∧ digit < 10) :
    0 ≤ sum (sublist 0 (digit+1) histogram) ∧ sum (sublist 0 (digit+1) histogram) ≤ hi := by
  let source_prefix := sublist 0 hi values
  have hplen : Zlength source_prefix = hi := by
    have h : Zlength source_prefix = hi - 0 := ListLib.Zlength_sublist 0 hi values (by omega) (by change hi ≤ Zlength values; omega)
    omega
  have hph : DigitHistogramPrefix source_prefix exponent (Zlength source_prefix) histogram := by
    intro d hb
    simpa only [RadixDigitCount, sublist_self source_prefix (Zlength source_prefix) rfl] using hh d hb
  have hs := histogram_start_as_prefix_length__stable_placement source_prefix exponent histogram (digit+1) hhlen hph (by omega)
  have hp := radix_stable_output_permutation__stable_placement source_prefix exponent (fun _ _ => digit_range _ _)
  have hp_len : Zlength (RadixStableOutput source_prefix exponent) = hi := by unfold Zlength; rw [← hp.length_eq]; exact hplen
  have hsplit : ([0,1,2,3,4,5,6,7,8,9] : List Int) =
    sublist 0 (digit+1) [0,1,2,3,4,5,6,7,8,9] ++ sublist (digit+1) 10 [0,1,2,3,4,5,6,7,8,9] := by
    rw [← sublist_split 0 10 (digit+1) ([0,1,2,3,4,5,6,7,8,9] : List Int) (by omega) (by change digit+1 ≤ 10 ∧ 10 ≤ 10; omega)]
    rfl
  have hout : RadixStableOutput source_prefix exponent =
    ((sublist 0 (digit+1) [0,1,2,3,4,5,6,7,8,9]).map (fun d => RadixBucket source_prefix exponent d)).flatten ++
    ((sublist (digit+1) 10 [0,1,2,3,4,5,6,7,8,9]).map (fun d => RadixBucket source_prefix exponent d)).flatten := by
    unfold RadixStableOutput
    conv => lhs; rw [hsplit, List.map_append, List.flatten_append]
  rw [hout, Zlength_app] at hp_len
  have hnonneg := Zlength_nonneg (((sublist 0 (digit+1) [0,1,2,3,4,5,6,7,8,9]).map (fun d => RadixBucket source_prefix exponent d)).flatten)
  have hrest := Zlength_nonneg (((sublist (digit+1) 10 [0,1,2,3,4,5,6,7,8,9]).map (fun d => RadixBucket source_prefix exponent d)).flatten)
  change sum (sublist 0 (digit+1) histogram) = _ at hs
  omega

private theorem mixed_some_index_lt (xs : List (Option Int)) (index value : Int)
    (hi : 0 ≤ index) (hv : Znth index xs none = some value) : index < Zlength xs := by
  by_cases hlt : index < Zlength xs
  · exact hlt
  · have hn : xs.length ≤ index.toNat := by simp only [Zlength, Int.ofNat_eq_coe] at hlt; omega
    have he : Znth index xs none = none := by
      simp only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_none hn, Option.getD_none]
    rw [he] at hv
    cases hv

theorem bucket_placement_step__stable_placement (source : List Int) (exponent : Int) (histogram counters : List Int)
    (mixed_output : List (Option Int)) (index : Int) (hlh : Zlength histogram = 10) (hlc : Zlength counters = 10)
    (hi : 0 ≤ index ∧ index < Zlength source)
    (hd : 0 ≤ RadixDigit (Znth index source 0) exponent ∧ RadixDigit (Znth index source 0) exponent < 10)
    (hh : DigitHistogramPrefix source exponent (Zlength source) histogram)
    (hp : BucketPlacementProgress source exponent (index+1) histogram counters mixed_output) :
    let digit := RadixDigit (Znth index source 0) exponent
    let next_counters := replace_Znth digit (Znth digit counters 0 - 1) counters
    let write_index := Znth digit next_counters 0
    (0 ≤ write_index ∧ write_index < 1000) → BucketPlacementProgress source exponent index histogram next_counters
      (replace_Znth write_index (some (Znth index source 0)) mixed_output) := by
  let digit := RadixDigit (Znth index source 0) exponent
  let next_counters := replace_Znth digit (Znth digit counters 0 - 1) counters
  let write_index := Znth digit next_counters 0
  change (0 ≤ write_index ∧ write_index < 1000) → BucketPlacementProgress source exponent index histogram next_counters
    (replace_Znth write_index (some (Znth index source 0)) mixed_output)
  intro hw
  have hdr : 0 ≤ digit ∧ digit < 10 := hd
  have hnext : Znth digit next_counters 0 = Znth digit counters 0 - 1 := Znth_replace_Znth_Same 0 counters digit _ (by omega)
  have hwrite : write_index = Znth digit counters 0 - 1 := hnext
  have hdiff : ∀ bucket, (0 ≤ bucket ∧ bucket < 10) → bucket ≠ digit → Znth bucket next_counters 0 = Znth bucket counters 0 := by
    intro bucket hb hne
    exact Znth_replace_Znth_Diff 0 counters digit bucket _ (by omega) (by omega) (Ne.symm hne)
  have hcounter : ∀ bucket, (0 ≤ bucket ∧ bucket < 10) →
      Znth bucket next_counters 0 = RadixBucketStart histogram bucket + RadixDigitCount source exponent index bucket := by
    intro bucket hb
    have hstep := radix_digit_count_step__stable_placement source exponent index bucket hi
    by_cases heq : bucket = digit
    · subst bucket
      have he : RadixDigit (Znth index source 0) exponent = digit := rfl
      simp only [he, decide_true, ↓reduceIte] at hstep
      rw [hnext, hp.2.1 digit hdr, hstep]
      omega
    · have hne : RadixDigit (Znth index source 0) exponent ≠ bucket := Ne.symm heq
      simp only [decide_eq_false hne, Bool.false_eq_true, ↓reduceIte, Int.add_zero] at hstep
      rw [hdiff bucket hb heq, hp.2.1 bucket hb, hstep]
  have hfull : ∀ bucket, RadixDigitCount source exponent (Zlength source) bucket = Zlength (RadixBucket source exponent bucket) := by
    intro bucket; unfold RadixDigitCount; rw [sublist_self source (Zlength source) rfl]
  have hbounds : ∀ bucket, (0 ≤ bucket ∧ bucket < 10) →
      RadixBucketStart histogram bucket ≤ Znth bucket next_counters 0 ∧ Znth bucket next_counters 0 ≤ RadixBucketEnd histogram bucket := by
    intro bucket hb
    rw [hcounter bucket hb]
    have hn : 0 ≤ RadixDigitCount source exponent index bucket := Zlength_nonneg _
    have hm := radix_digit_count_prefix_le_full__stable_placement source exponent index bucket (by omega)
    rw [hfull bucket] at hm
    have he := bucket_end_start_count__stable_placement source exponent histogram bucket hlh hh hb
    omega
  have hcurrent := (radix_bucket_current_position__stable_placement source exponent index digit hi rfl).2
  rw [hfull digit] at hcurrent
  have hend := bucket_end_start_count__stable_placement source exponent histogram digit hlh hh hdr
  have hwrite_counter : write_index = RadixBucketStart histogram digit + RadixDigitCount source exponent index digit := hcounter digit hdr
  have hcount_nonneg : 0 ≤ RadixDigitCount source exponent index digit := Zlength_nonneg _
  have hwrite_range : RadixBucketStart histogram digit ≤ write_index ∧ write_index < RadixBucketEnd histogram digit := by omega
  have hstable : Znth write_index (RadixStableOutput source exponent) 0 = Znth index source 0 := by
    rw [hwrite_counter]
    exact radix_current_stable_position__stable_placement source exponent histogram index hlh hh hi hd
  have hwrite_valid : 0 ≤ write_index ∧ write_index < Zlength mixed_output := by have := hp.1; omega
  have hstart_nonneg : ∀ bucket, (0 ≤ bucket ∧ bucket < 10) → 0 ≤ RadixBucketStart histogram bucket := by
    intro bucket hb
    exact histogram_sublist_sum_nonnegative__stable_placement source exponent histogram 0 bucket hlh hh (by omega) (by omega)
  refine ⟨by simpa only [Zlength_replace_Znth] using hp.1, hcounter, hbounds, ?_, ?_⟩
  · intro bucket pos hb hpos
    by_cases heq : pos = write_index
    · subst pos
      rw [Znth_replace_Znth_Same none mixed_output write_index _ hwrite_valid, hstable]
    · have hold_range : Znth bucket counters 0 ≤ pos ∧ pos < RadixBucketEnd histogram bucket := by
        by_cases hbd : bucket = digit
        · subst bucket; rw [hnext] at hpos; omega
        · rw [hdiff bucket hb hbd] at hpos; exact hpos
      have hold := hp.2.2.2.1 bucket pos hb hold_range
      have hpos_nonneg : 0 ≤ pos := by
        have := hbounds bucket hb
        have := hstart_nonneg bucket hb
        omega
      have hpos_valid : 0 ≤ pos ∧ pos < Zlength mixed_output := ⟨hpos_nonneg, mixed_some_index_lt mixed_output pos _ hpos_nonneg hold⟩
      rw [Znth_replace_Znth_Diff none mixed_output write_index pos _ hwrite_valid hpos_valid (Ne.symm heq)]
      exact hold
  · intro pos hpos hall
    have heq : pos ≠ write_index := by
      intro heq; subst pos
      have h := hall digit hdr
      change write_index < write_index ∨ RadixBucketEnd histogram digit ≤ write_index at h
      omega
    have holdall : ∀ bucket, (0 ≤ bucket ∧ bucket < 10) → pos < Znth bucket counters 0 ∨ RadixBucketEnd histogram bucket ≤ pos := by
      intro bucket hb
      have h := hall bucket hb
      by_cases hbd : bucket = digit
      · subst bucket; rw [hnext] at h; omega
      · rw [hdiff bucket hb hbd] at h; exact h
    rw [Znth_replace_Znth_Diff none mixed_output write_index pos _ hwrite_valid (by have := hp.1; omega) (Ne.symm heq)]
    exact hp.2.2.2.2 pos hpos holdall

end SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib

namespace SimpleC.EE.LLM_bench.Algorithms.bucket_sort
export bucket_sort_lib (RadixDigit PrefixMaximum DecimalExponent RadixLowerDigitsOrdered RadixPassState RadixBucket RadixDigitCount
  DigitHistogramPrefix DigitPrefixTotals RadixBucketStart RadixBucketEnd RadixStableOutput StableDigitPass BucketPlacementProgress
  RadixCopyPrefix Some None _App_option_Z increasing increasing_aux lowerbound upperbound StronglySorted SSorted_nil SSorted_cons)
end SimpleC.EE.LLM_bench.Algorithms.bucket_sort
