import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_table_budget

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

namespace P090_DivisorEnumeration

private theorem add_eq_plus (a b : Int) : Int.add a b=a+b := rfl

theorem exponent_trace_lengths (pr pe exponents : List Int) (product : Int) :
    ExponentTrace pr pe exponents product → pr.length=pe.length ∧ exponents.length=pr.length := by
  intro h
  induction h with
  | exponent_trace_nil => simp
  | exponent_trace_cons p pr m pe e ex d he ht ih => simp only [List.length_cons]; omega

theorem exponent_trace_product_functional (pr pe exponents : List Int) (a b : Int) :
    ExponentTrace pr pe exponents a → ExponentTrace pr pe exponents b → a=b := by
  intro ha
  induction ha generalizing b with
  | exponent_trace_nil => intro hb; cases hb; rfl
  | exponent_trace_cons p pr m pe e ex d he ht ih =>
    intro hb
    cases hb with
    | exponent_trace_cons _ _ _ _ _ _ b he' ht' => rw [ih b ht']

theorem enumerated_products_trace (pr pe : List Int) (product : Int) :
    Zlength pr=Zlength pe → Forall (fun e=>0≤e) pe →
    (product∈enumerated_products pr pe ↔ ∃ exponents, ExponentTrace pr pe exponents product) := by
  induction pr generalizing pe product with
  | nil =>
    intro hl hn
    cases pe with
    | nil =>
      simp only [enumerated_products,List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨[],.exponent_trace_nil⟩
      · rintro ⟨ex,h⟩; cases h; rfl
    | cons m pe => simp [Zlength] at hl; omega
  | cons p pr ih =>
    intro hl hn
    cases pe with
    | nil => simp [Zlength] at hl; omega
    | cons m pe =>
      have htlen : Zlength pr=Zlength pe := by rw [Zlength_cons,Zlength_cons] at hl; omega
      cases hn with
      | cons hm ht =>
        rw [enumerated_products,List.mem_flatten]
        constructor
        · rintro ⟨block,hblock,hin⟩
          obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hblock
          obtain ⟨tail,htail,rfl⟩ := List.mem_map.mp hin
          obtain ⟨ex,htrace⟩ := (ih pe tail htlen ht).mp htail
          have hnlt : n<Nat.succ m.toNat := by
            obtain ⟨j,hj,hjn⟩ := List.mem_range'.mp hn
            omega
          refine ⟨Int.ofNat n::ex,.exponent_trace_cons p pr m pe (Int.ofNat n) ex tail ?_ htrace⟩
          simp only [Int.ofNat_eq_coe]
          omega
        · rintro ⟨ex,htrace⟩
          cases htrace with
          | exponent_trace_cons _ _ _ _ e ex tail he htail =>
            refine ⟨(enumerated_products pr pe).map (fun t=>Z.pow p (Int.ofNat e.toNat)*t), ?_, ?_⟩
            · apply List.mem_map.mpr
              refine ⟨e.toNat,?_,rfl⟩
              apply List.mem_range'.mpr
              exact ⟨e.toNat,by omega,by omega⟩
            · apply List.mem_map.mpr
              have hc : Int.ofNat e.toNat=e := by simpa using Int.toNat_of_nonneg he.1
              exact ⟨tail,(ih pe tail htlen ht).mpr ⟨ex,htail⟩,by rw [hc]⟩

theorem valid_factor_table_exponents_nonnegative (m : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → Forall (fun e=>0≤e) pe := by
  intro h
  have ht := valid_factor_table_ordered m pr pe h
  clear h
  induction ht with
  | ordered_prime_table_nil => exact .nil
  | ordered_prime_table_cons p e pr pe hp he hl ht ih => exact .cons (by omega) ih

theorem valid_factor_table_exact_trace_enumeration (m : Int) (pr pe : List Int) (product : Int) :
    ValidFactorTable m pr pe → (product∈enumerated_products pr pe ↔
      ∃ exponents, ExponentTrace pr pe exponents product ∧ Zlength exponents=Zlength pr) := by
  intro h
  rw [enumerated_products_trace pr pe product h.1 (valid_factor_table_exponents_nonnegative m pr pe h)]
  constructor
  · rintro ⟨ex,ht⟩
    exact ⟨ex,ht,by unfold Zlength; rw [(exponent_trace_lengths pr pe ex product ht).2]⟩
  · rintro ⟨ex,ht,hl⟩; exact ⟨ex,ht⟩

theorem sum_nat_range_as_seq (first count : Nat) (f : Nat→Int) :
    sum_nat_range first count f=((List.range' first count).map f).foldr Int.add 0 := by
  induction count generalizing first with
  | zero => rfl
  | succ n ih => rw [sum_nat_range,List.range'_succ]; simp only [List.map_cons,List.foldr_cons]; rw [ih]; rfl

theorem fold_right_add_acc (values : List Int) (accumulator : Int) :
    values.foldr Int.add accumulator=values.foldr Int.add 0+accumulator := by
  induction values with
  | nil => simp
  | cons v vs ih => simp only [List.foldr_cons,add_eq_plus]; rw [ih]; ring

theorem fold_right_concat_map {A : Type} (blocks : List A) (f : A→List Int) :
    ((blocks.map f).flatten).foldr Int.add 0=(blocks.map (fun a=>(f a).foldr Int.add 0)).foldr Int.add 0 := by
  induction blocks with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.flatten_cons,List.foldr_cons,List.foldr_append]
    rw [ih,fold_right_add_acc]
    rfl

theorem walk_suffix_lists_exact_terms (pr pe : List Int) (x d : Int) :
    walk_suffix_lists pr pe x d=(enumerated_walk_terms pr pe x d).foldr Int.add 0 := by
  induction pr generalizing pe d with
  | nil => cases pe <;> simp [walk_suffix_lists,enumerated_walk_terms]
  | cons p pr ih =>
    cases pe with
    | nil => simp [walk_suffix_lists,enumerated_walk_terms]
    | cons m pe =>
      rw [walk_suffix_lists,sum_nat_range_as_seq,enumerated_walk_terms,fold_right_concat_map]
      apply congrArg (List.foldr Int.add 0)
      apply List.map_congr_left
      intro n hn
      exact ih pe _

theorem enumerated_walk_terms_as_products (pr pe : List Int) (x d : Int) :
    enumerated_walk_terms pr pe x d=(enumerated_products pr pe).map (fun product=>CycleTerm x (d*product)) := by
  induction pr generalizing pe d with
  | nil => cases pe <;> simp [enumerated_walk_terms,enumerated_products]
  | cons p pr ih =>
    cases pe with
    | nil => simp [enumerated_walk_terms,enumerated_products]
    | cons m pe =>
      rw [enumerated_walk_terms,enumerated_products,List.map_flatten,List.map_map]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro n hn
      dsimp only [Function.comp_def]
      rw [ih,List.map_map]
      apply List.map_congr_left
      intro t ht
      dsimp only [Function.comp_def]
      rw [mul_assoc]

theorem walk_suffix_exact_divisor_cycle_sum (pr pe : List Int) (x i d : Int) :
    WalkSuffix pr pe x i d=((enumerated_products (pr.drop i.toNat) (pe.drop i.toNat)).map
      (fun product=>CycleTerm x (d*product))).foldr Int.add 0 := by
  unfold WalkSuffix
  rw [walk_suffix_lists_exact_terms,enumerated_walk_terms_as_products]

theorem cycle_term_one (x : Int) : CycleTerm x 1=0 := rfl

theorem fold_filter_cycle_term_one (x : Int) (products : List Int) :
    (products.map (CycleTerm x)).foldr Int.add 0=
      ((products.filter (fun d=>!(d==1))).map (CycleTerm x)).foldr Int.add 0 := by
  induction products with
  | nil => rfl
  | cons d ds ih =>
    by_cases hd : d=1
    · subst d
      simp [cycle_term_one,ih]
    · simp [hd,ih]

theorem walk_suffix_zero_is_nonunit_cycle_sum (pr pe : List Int) (x : Int) :
    WalkSuffix pr pe x 0 1=NonUnitDivisorCycleSum pr pe x := by
  rw [walk_suffix_exact_divisor_cycle_sum]
  simpa [NonUnitDivisorCycleSum] using fold_filter_cycle_term_one x (enumerated_products pr pe)

theorem walk_budget_nonunit_cycle_interface (m : Int) (pr pe : List Int) (x : Int) :
    WalkBudget m 0 (WalkSuffix pr pe x 0 1) ↔ (0≤NonUnitDivisorCycleSum pr pe x ∧ NonUnitDivisorCycleSum pr pe x≤m) := by
  rw [walk_suffix_zero_is_nonunit_cycle_sum]
  simp [WalkBudget]

theorem prefix_selected_trace_forget (pr pe : List Int) (i : Int) (exponents : List Int) (d : Int) :
    PrefixSelectedTrace pr pe i exponents d → PrefixSelected pr pe i d := by
  intro h
  induction h with
  | prefix_selected_trace_zero => exact .prefix_selected_zero
  | prefix_selected_trace_step i ex d e ht hi he ih => exact .prefix_selected_step i d e ih hi he

theorem prefix_selected_has_trace (pr pe : List Int) (i d : Int) :
    PrefixSelected pr pe i d → ∃ exponents, PrefixSelectedTrace pr pe i exponents d := by
  intro h
  induction h with
  | prefix_selected_zero => exact ⟨[],.prefix_selected_trace_zero⟩
  | prefix_selected_step i d e hs hi he ih =>
    obtain ⟨ex,ht⟩ := ih
    exact ⟨ex++[e],.prefix_selected_trace_step i ex d e ht hi he⟩

theorem prefix_selected_trace_length (pr pe : List Int) (i : Int) (exponents : List Int) (d : Int) :
    PrefixSelectedTrace pr pe i exponents d → Zlength exponents=i := by
  intro h
  induction h with
  | prefix_selected_trace_zero => rfl
  | prefix_selected_trace_step i ex d e ht hi he ih => simpa [Zlength] using ih

theorem prefix_selected_exact_trace_interface (pr pe : List Int) (i d : Int) :
    PrefixSelected pr pe i d ↔ ∃ exponents, PrefixSelectedTrace pr pe i exponents d ∧ Zlength exponents=i := by
  constructor
  · intro h
    obtain ⟨ex,ht⟩ := prefix_selected_has_trace pr pe i d h
    exact ⟨ex,ht,prefix_selected_trace_length pr pe i ex d ht⟩
  · rintro ⟨ex,ht,hl⟩
    exact prefix_selected_trace_forget pr pe i ex d ht

end P090_DivisorEnumeration
export P090_DivisorEnumeration (exponent_trace_lengths exponent_trace_product_functional enumerated_products_trace valid_factor_table_exponents_nonnegative valid_factor_table_exact_trace_enumeration sum_nat_range_as_seq fold_right_add_acc fold_right_concat_map walk_suffix_lists_exact_terms enumerated_walk_terms_as_products walk_suffix_exact_divisor_cycle_sum cycle_term_one fold_filter_cycle_term_one walk_suffix_zero_is_nonunit_cycle_sum walk_budget_nonunit_cycle_interface prefix_selected_trace_forget prefix_selected_has_trace prefix_selected_trace_length prefix_selected_exact_trace_interface)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
