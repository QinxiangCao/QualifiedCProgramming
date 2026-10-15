import Mathlib.Data.List.Nodup
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_divisor_factorization

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

namespace P090_DivisorCompleteness

private theorem strict_exponents_force_divisor (p e f a b : Int) (hp : 0<p) (he : 0≤e) (hef : e<f)
    (h : Z.pow p e*a=Z.pow p f*b) : p ∣ᶻ a := by
  have hdiff : 1≤f-e := by omega
  have hcancel : a=Z.pow p (f-e)*b := by
    apply mul_left_cancel₀ (ne_of_gt (coq_pow_pos p e hp he))
    rw [← mul_assoc,← coq_pow_add p e (f-e) he (by omega)]
    simpa only [show e+(f-e)=f by omega] using h
  have hd := coq_pow_divides_pow p 1 (f-e) (by omega) hdiff
  have hp1 : Z.pow p 1=p := by simp [Z.pow]
  rw [hp1] at hd
  apply (Z.divide_iff_dvd _ _).mpr
  rw [hcancel]
  exact dvd_mul_of_dvd_left ((Z.divide_iff_dvd _ _).mp hd) b

theorem prime_power_residual_unique (p e f a b : Int) :
    prime p → 0≤e → 0≤f → 0<a → 0<b → ¬(p ∣ᶻ a) → ¬(p ∣ᶻ b) →
    Z.pow p e*a=Z.pow p f*b → e=f ∧ a=b := by
  intro hp he hf ha hb hpa hpb hpow
  have hp2 := prime_ge_2 p hp
  have hef : e=f := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact hpa (strict_exponents_force_divisor p e f a b (by omega) he hlt hpow)
    · exact hpb (strict_exponents_force_divisor p f e b a (by omega) hf hgt hpow.symm)
  refine ⟨hef,?_⟩
  subst f
  exact mul_left_cancel₀ (ne_of_gt (coq_pow_pos p e (by omega) he)) hpow

theorem exponent_trace_positive (pr pe exponents : List Int) (product : Int) :
    CanonicalFactorTable pr pe → ExponentTrace pr pe exponents product → 0<product := by
  intro ht hx
  induction hx with
  | exponent_trace_nil => omega
  | exponent_trace_cons p pr m pe e ex d he hx ih =>
    cases ht with
    | canonical_factor_table_cons _ _ _ _ hp hm ht hn =>
      exact mul_pos (coq_pow_pos p e (by have := prime_ge_2 p hp; omega) he.1) (ih ht)

theorem exponent_trace_divides_factor_product (pr pe exponents : List Int) (product : Int) :
    CanonicalFactorTable pr pe → ExponentTrace pr pe exponents product → (product ∣ᶻ factor_product pr pe) := by
  intro ht hx
  induction hx with
  | exponent_trace_nil => exact ⟨1,by simp [factor_product]⟩
  | exponent_trace_cons p pr m pe e ex d he hx ih =>
    cases ht with
    | canonical_factor_table_cons _ _ _ _ hp hm ht hn =>
      obtain ⟨tail,htail⟩ := ih ht
      obtain ⟨head,hhead⟩ := coq_pow_divides_pow p e m he.1 he.2
      refine ⟨head*tail,?_⟩
      change Z.pow p m*factor_product pr pe=(head*tail)*(Z.pow p e*d)
      rw [hhead,htail]
      ring

theorem exponent_trace_cons_inv (p : Int) (pr : List Int) (maximum : Int) (pe exponents : List Int) (product : Int) :
    ExponentTrace (p::pr) (maximum::pe) exponents product →
    ∃ exponent tail_exponents tail_product, exponents=exponent::tail_exponents ∧ product=Z.pow p exponent*tail_product ∧
      (0≤exponent ∧ exponent≤maximum) ∧ ExponentTrace pr pe tail_exponents tail_product := by
  intro h
  cases h with
  | exponent_trace_cons _ _ _ _ e ex d he ht => exact ⟨e,ex,d,rfl,rfl,he,ht⟩

theorem canonical_exponent_trace_unique (pr pe exponents1 exponents2 : List Int) (product : Int) :
    CanonicalFactorTable pr pe → ExponentTrace pr pe exponents1 product → ExponentTrace pr pe exponents2 product → exponents1=exponents2 := by
  intro ht
  induction ht generalizing exponents1 exponents2 product with
  | canonical_factor_table_nil => intro h1 h2; cases h1; cases h2; rfl
  | canonical_factor_table_cons p pr m pe hp hm ht hn ih =>
    intro h1 h2
    obtain ⟨e1,ex1,d1,rfl,hd1,he1,ht1⟩ := exponent_trace_cons_inv p pr m pe exponents1 product h1
    obtain ⟨e2,ex2,d2,rfl,hd2,he2,ht2⟩ := exponent_trace_cons_inv p pr m pe exponents2 product h2
    have hpos1 := exponent_trace_positive pr pe ex1 d1 ht ht1
    have hpos2 := exponent_trace_positive pr pe ex2 d2 ht ht2
    have hnd1 : ¬(p ∣ᶻ d1) := by
      intro hdiv
      exact hn ((Z.divide_iff_dvd _ _).mpr (dvd_trans ((Z.divide_iff_dvd _ _).mp hdiv)
        ((Z.divide_iff_dvd _ _).mp (exponent_trace_divides_factor_product pr pe ex1 d1 ht ht1))))
    have hnd2 : ¬(p ∣ᶻ d2) := by
      intro hdiv
      exact hn ((Z.divide_iff_dvd _ _).mpr (dvd_trans ((Z.divide_iff_dvd _ _).mp hdiv)
        ((Z.divide_iff_dvd _ _).mp (exponent_trace_divides_factor_product pr pe ex2 d2 ht ht2))))
    obtain ⟨heq,hdq⟩ := prime_power_residual_unique p e1 e2 d1 d2 hp he1.1 he2.1 hpos1 hpos2 hnd1 hnd2 (hd1.symm.trans hd2)
    subst e2 d2
    exact congrArg (List.cons e1) (ih ex1 ex2 d1 ht1 ht2)

theorem valid_factor_table_exponent_vector_unique (m : Int) (pr pe exponents1 exponents2 : List Int) (product : Int) :
    ValidFactorTable m pr pe → ExponentTrace pr pe exponents1 product → ExponentTrace pr pe exponents2 product → exponents1=exponents2 := by
  intro ht
  exact canonical_exponent_trace_unique pr pe exponents1 exponents2 product (valid_factor_table_canonical m pr pe ht)

theorem map_injective_nodup {A B : Type} (f : A→B) (xs : List A) :
    (∀ x y, x∈xs → y∈xs → f x=f y → x=y) → NoDup xs → NoDup (xs.map f) := by
  intro hf hn
  exact List.Nodup.map_on (by intro x hx y hy he; exact hf x y hx hy he) hn

theorem tagged_vectors_nodup (tags : List Nat) (tails : List (List Int)) :
    NoDup tags → NoDup tails → NoDup ((tags.map (fun tag=>tails.map (List.cons (Int.ofNat tag)))).flatten) := by
  intro htags htails
  induction tags with
  | nil => simp
  | cons tag tags ih =>
    have htag := List.nodup_cons.mp htags
    simp only [List.map_cons,List.flatten_cons]
    apply List.Nodup.append
    · apply map_injective_nodup _ tails ?_ htails
      intro a b ha hb he
      exact (List.cons.inj he).2
    · exact ih htag.2
    · intro v hv hvs
      obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp hv
      obtain ⟨block,hblock,hin⟩ := List.mem_flatten.mp hvs
      obtain ⟨tag',htag',rfl⟩ := List.mem_map.mp hblock
      obtain ⟨tail',ht',heq⟩ := List.mem_map.mp hin
      have he := (List.cons.inj heq).1
      have he' : tag'=tag := Int.ofNat.inj he
      exact htag.1 (he' ▸ htag')

theorem enumerated_exponent_vectors_nodup (pe : List Int) : NoDup (enumerated_exponent_vectors pe) := by
  induction pe with
  | nil => simp [enumerated_exponent_vectors]
  | cons m pe ih =>
    apply tagged_vectors_nodup
    · exact List.nodup_range' _ (by omega)
    · exact ih

theorem enumerated_products_as_vector_map (pr pe : List Int) :
    Zlength pr=Zlength pe → enumerated_products pr pe=(enumerated_exponent_vectors pe).map (exponent_vector_product pr) := by
  induction pr generalizing pe with
  | nil =>
    intro hl
    cases pe with
    | nil => rfl
    | cons m pe => simp [Zlength] at hl; omega
  | cons p pr ih =>
    intro hl
    cases pe with
    | nil => simp [Zlength] at hl; omega
    | cons m pe =>
      have htlen : Zlength pr=Zlength pe := by rw [Zlength_cons,Zlength_cons] at hl; omega
      rw [enumerated_products,enumerated_exponent_vectors,List.map_flatten,List.map_map]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro n hn
      dsimp only [Function.comp_def]
      rw [ih pe htlen,List.map_map,List.map_map]
      apply List.map_congr_left
      intro tail ht
      rfl

theorem enumerated_vector_has_trace (pr pe exponents : List Int) :
    Zlength pr=Zlength pe → Forall (fun m=>0≤m) pe → exponents∈enumerated_exponent_vectors pe →
    ExponentTrace pr pe exponents (exponent_vector_product pr exponents) := by
  induction pr generalizing pe exponents with
  | nil =>
    intro hl hn hin
    cases pe with
    | nil =>
      have he : exponents=[] := by simpa [enumerated_exponent_vectors] using hin
      subst exponents
      exact .exponent_trace_nil
    | cons m pe => simp [Zlength] at hl; omega
  | cons p pr ih =>
    intro hl hn hin
    cases pe with
    | nil => simp [Zlength] at hl; omega
    | cons m pe =>
      cases hn with
      | cons hm ht =>
        rw [enumerated_exponent_vectors] at hin
        obtain ⟨block,hblock,hin⟩ := List.mem_flatten.mp hin
        obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hblock
        obtain ⟨tail,htail,rfl⟩ := List.mem_map.mp hin
        refine .exponent_trace_cons p pr m pe (Int.ofNat n) tail (exponent_vector_product pr tail) ?_ ?_
        · obtain ⟨j,hj,hjn⟩ := List.mem_range'.mp hn
          simp only [Int.ofNat_eq_coe]
          omega
        · apply ih pe tail (by rw [Zlength_cons,Zlength_cons] at hl; omega) ht htail

theorem valid_factor_table_enumerated_products_nodup (m : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → NoDup (enumerated_products pr pe) := by
  intro ht
  rw [enumerated_products_as_vector_map pr pe ht.1]
  apply map_injective_nodup
  · intro e1 e2 h1 h2 he
    have hnon := valid_factor_table_exponents_nonnegative m pr pe ht
    apply valid_factor_table_exponent_vector_unique m pr pe e1 e2 (exponent_vector_product pr e1) ht
    · exact enumerated_vector_has_trace pr pe e1 ht.1 hnon h1
    · rw [he]
      exact enumerated_vector_has_trace pr pe e2 ht.1 hnon h2
  · exact enumerated_exponent_vectors_nodup pe

theorem valid_factor_table_exact_positive_divisor_bijection (m : Int) (pr pe : List Int) (divisor : Int) :
    ValidFactorTable m pr pe → (divisor∈enumerated_products pr pe ↔ 0<divisor ∧ (divisor ∣ᶻ m)) := by
  intro ht
  constructor
  · intro hin
    obtain ⟨ex,htrace,hlen⟩ := (valid_factor_table_exact_trace_enumeration m pr pe divisor ht).mp hin
    refine ⟨exponent_trace_positive pr pe ex divisor (valid_factor_table_canonical m pr pe ht) htrace,?_⟩
    rw [ht.2.2.1]
    exact exponent_trace_divides_factor_product pr pe ex divisor (valid_factor_table_canonical m pr pe ht) htrace
  · rintro ⟨hp,hd⟩
    obtain ⟨ex,htrace⟩ := valid_factor_table_divisor_complete m pr pe divisor ht hp hd
    apply (valid_factor_table_exact_trace_enumeration m pr pe divisor ht).mpr
    exact ⟨ex,htrace,by unfold Zlength; rw [(exponent_trace_lengths pr pe ex divisor htrace).2]⟩

end P090_DivisorCompleteness
export P090_DivisorCompleteness (prime_power_residual_unique exponent_trace_positive exponent_trace_divides_factor_product exponent_trace_cons_inv canonical_exponent_trace_unique valid_factor_table_exponent_vector_unique map_injective_nodup tagged_vectors_nodup enumerated_exponent_vectors_nodup enumerated_products_as_vector_map enumerated_vector_has_trace valid_factor_table_enumerated_products_nodup valid_factor_table_exact_positive_divisor_bijection)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
