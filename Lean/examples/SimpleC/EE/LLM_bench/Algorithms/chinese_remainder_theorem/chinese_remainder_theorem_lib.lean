import AUXLib.NumberTheory
import AUXLib.ListLib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_lib
open AUXLib

def CRTProduct (moduli : List Int) : Int := moduli.foldr (· * ·) 1

def CRTInputValid (remainders moduli : List Int) : Prop :=
  Zlength remainders = Zlength moduli ∧ 1 ≤ Zlength moduli ∧
  (∀ i, (0 ≤ i ∧ i < Zlength moduli) →
    1 ≤ Znth i moduli 0 ∧ 0 ≤ Znth i remainders 0 ∧ Znth i remainders 0 < Znth i moduli 0) ∧
  (∀ i j, (0 ≤ i ∧ i < j ∧ j < Zlength moduli) → Z.gcd (Znth i moduli 0) (Znth j moduli 0) = 1)

def CRTMachineSafe (remainders moduli : List Int) : Prop :=
  let product := CRTProduct moduli
  (1 ≤ product ∧ product ≤ 46340) ∧
  (∀ i coefficient, (0 ≤ i ∧ i < Zlength moduli) →
    (-2147483648 ≤ coefficient ∧ coefficient ≤ 2147483647) →
    -2147483648 ≤ coefficient * Z.div product (Znth i moduli 0) ∧
    coefficient * Z.div product (Znth i moduli 0) ≤ 2147483647)

def CanonicalCRTSolution (remainders moduli : List Int) (answer : Int) : Prop :=
  (0 ≤ answer ∧ answer < CRTProduct moduli) ∧
  ∀ i, (0 ≤ i ∧ i < Zlength moduli) → Z.modulo answer (Znth i moduli 0) = Znth i remainders 0

def CRTProcessedCongruences (remainders moduli : List Int) (processed result : Int) : Prop :=
  ∀ i, (0 ≤ i ∧ i < processed) → Z.modulo result (Znth i moduli 0) = Znth i remainders 0

theorem fold_right_mul_acc__product_progress (l : List Int) (acc : Int) :
    l.foldr (· * ·) acc = l.foldr (· * ·) 1 * acc := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.foldr_cons, ih, Int.mul_assoc]

theorem crt_prefix_product_step__product_progress (moduli : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength moduli) :
    CRTProduct (sublist 0 (i+1) moduli) = CRTProduct (sublist 0 i moduli) * Znth i moduli 0 := by
  rw [sublist_split 0 (i+1) i moduli (by omega) (by omega), sublist_single 0 i moduli hi]
  unfold CRTProduct
  rw [List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil, Int.mul_one]
  exact fold_right_mul_acc__product_progress _ _

theorem crt_product_app__product_progress (left right : List Int) :
    CRTProduct (left++right) = CRTProduct left * CRTProduct right := by
  unfold CRTProduct
  rw [List.foldr_append]
  exact fold_right_mul_acc__product_progress _ _

theorem crt_input_moduli_positive__product_progress (remainders moduli : List Int)
    (hv : CRTInputValid remainders moduli) : Forall (fun modulus => 1 ≤ modulus) moduli := by
  apply Forall.iff_forall_mem.mpr
  intro modulus hm
  obtain ⟨n, hn, he⟩ := List.mem_iff_getElem.mp hm
  have hi : 0 ≤ (n : Int) ∧ (n : Int) < Zlength moduli := by simp only [Zlength, Int.ofNat_eq_coe]; omega
  have h := (hv.2.2.1 (n : Int) hi).1
  simpa [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, he] using h

theorem crt_product_positive__product_progress (moduli : List Int)
    (hp : Forall (fun modulus => 1 ≤ modulus) moduli) : 1 ≤ CRTProduct moduli := by
  induction hp with
  | nil => decide
  | @cons m ms hm hms ih =>
    change 1 ≤ m * CRTProduct ms
    have h := Int.mul_le_mul_of_nonneg_right hm (show 0 ≤ CRTProduct ms by omega)
    simp only [Int.one_mul] at h
    omega

theorem crt_prefix_product_bounds__product_progress (remainders moduli : List Int) (i : Int)
    (hv : CRTInputValid remainders moduli) (hi : 0 ≤ i ∧ i ≤ Zlength moduli) :
    (1 ≤ CRTProduct (sublist 0 i moduli) ∧ CRTProduct (sublist 0 i moduli) ≤ CRTProduct moduli) ∧
    (i = Zlength moduli → sublist 0 i moduli = moduli) := by
  have hs : moduli = sublist 0 i moduli ++ sublist i (Zlength moduli) moduli := by
    rw [← sublist_split 0 (Zlength moduli) i moduli (by omega) (by omega)]
    exact (sublist_self moduli (Zlength moduli) rfl).symm
  have hall := Forall.iff_forall_mem.mp (crt_input_moduli_positive__product_progress remainders moduli hv)
  have hp := crt_product_positive__product_progress (sublist 0 i moduli) (Forall.iff_forall_mem.mpr (by
    intro m hm; apply hall m; rw [hs]; exact List.mem_append_left _ hm))
  have ht := crt_product_positive__product_progress (sublist i (Zlength moduli) moduli) (Forall.iff_forall_mem.mpr (by
    intro m hm; apply hall m; rw [hs]; exact List.mem_append_right _ hm))
  have he : CRTProduct moduli = CRTProduct (sublist 0 i moduli) * CRTProduct (sublist i (Zlength moduli) moduli) := by
    conv => lhs; rw [hs]
    exact crt_product_app__product_progress _ _
  have h := Int.mul_le_mul_of_nonneg_left ht (show 0 ≤ CRTProduct (sublist 0 i moduli) by omega)
  simp only [Int.mul_one] at h
  exact ⟨⟨hp, by omega⟩, fun hi => sublist_self moduli i hi⟩

private theorem index_divides (l : List Int) (k : Int) (hk : 0 ≤ k ∧ k < Zlength l) :
    Z.divide (Znth k l 0) (l.foldr (· * ·) 1) := by
  induction l generalizing k with
  | nil => simp [Zlength] at hk; omega
  | cons a l ih =>
    rw [Zlength_cons] at hk
    by_cases he : k = 0
    · subst k
      rw [Znth0_cons]
      exact ⟨l.foldr (· * ·) 1, by simp [Int.mul_comm]⟩
    · rw [Znth_cons 0 k a l (by omega)]
      obtain ⟨q, hq⟩ := ih (k-1) (by omega)
      exact ⟨a*q, by simp only [List.foldr_cons]; rw [hq]; grind⟩

theorem crt_factor_quotient_bounds__product_progress (remainders moduli : List Int) (i : Int)
    (hv : CRTInputValid remainders moduli) (hi : 0 ≤ i ∧ i < Zlength moduli) :
    (1 ≤ Znth i moduli 0 ∧ Znth i moduli 0 ≤ CRTProduct moduli) ∧
    (1 ≤ Z.div (CRTProduct moduli) (Znth i moduli 0) ∧ Z.div (CRTProduct moduli) (Znth i moduli 0) ≤ CRTProduct moduli) := by
  have hm := (hv.2.2.1 i hi).1
  have hp := (crt_prefix_product_bounds__product_progress remainders moduli i hv (by omega)).1.1
  have hn := (crt_prefix_product_bounds__product_progress remainders moduli (i+1) hv (by omega)).1.2
  rw [crt_prefix_product_step__product_progress moduli i hi] at hn
  have ht := Int.mul_le_mul_of_nonneg_right hp (show 0 ≤ Znth i moduli 0 by omega)
  simp only [Int.one_mul] at ht
  have hbound : Znth i moduli 0 ≤ CRTProduct moduli := by omega
  obtain ⟨q, hq⟩ := index_divides moduli i hi
  change CRTProduct moduli = q * Znth i moduli 0 at hq
  have hqp := Int.pos_of_mul_pos_left (show 0 < q * Znth i moduli 0 by omega) (by omega)
  have hle := Int.mul_le_mul_of_nonneg_left hm (Int.le_of_lt hqp)
  simp only [Int.mul_one] at hle
  have hdiv : Z.div (CRTProduct moduli) (Znth i moduli 0) = q := by
    rw [hq]; exact Int.mul_fdiv_cancel q (by omega)
  exact ⟨⟨hm, hbound⟩, by rw [hdiv]; omega⟩

theorem CRTProduct_ge_one__machine_safety (moduli : List Int)
    (ha : ∀ modulus, modulus ∈ moduli → 1 ≤ modulus) : 1 ≤ CRTProduct moduli :=
  crt_product_positive__product_progress moduli (Forall.iff_forall_mem.mpr ha)

theorem CRTProduct_factor_upper_bound__machine_safety (moduli : List Int) (modulus : Int)
    (ha : ∀ x, x ∈ moduli → 1 ≤ x) (hm : modulus ∈ moduli) : modulus ≤ CRTProduct moduli := by
  induction moduli with
  | nil => simp at hm
  | cons head rest ih =>
    have hh := ha head (by simp)
    have ht : ∀ x, x ∈ rest → 1 ≤ x := fun x hx => ha x (List.mem_cons_of_mem _ hx)
    have hp := CRTProduct_ge_one__machine_safety rest ht
    change modulus ≤ head * CRTProduct rest
    have hprod := Int.mul_le_mul_of_nonneg_left hp (show 0 ≤ head by omega)
    have hrest := Int.mul_le_mul_of_nonneg_right hh (show 0 ≤ CRTProduct rest by omega)
    simp only [Int.mul_one, Int.one_mul] at hprod hrest
    rcases List.mem_cons.mp hm with rfl | hm
    · omega
    · have hf := ih ht hm; omega

theorem CRTInputValid_modulus_upper_bound__machine_safety (remainders moduli : List Int) (i : Int)
    (hv : CRTInputValid remainders moduli) (hi : 0 ≤ i ∧ i < Zlength moduli) :
    Znth i moduli 0 ≤ CRTProduct moduli :=
  (crt_factor_quotient_bounds__product_progress remainders moduli i hv hi).1.2

theorem crt_c_rem_mul_int_bounds__machine_safety (a product remainder : Int)
    (hp : 1 ≤ product) (hu : product ≤ 46340) (hr : 0 ≤ remainder) (hrp : remainder < product) :
    -2147483648 ≤ Z.rem a product * remainder ∧ Z.rem a product * remainder ≤ 2147483647 := by
  have hb := AUXLib.rem_bounds a product (by omega)
  have hlo := Int.mul_le_mul_of_nonneg_right (show (-46340 : Int) ≤ Z.rem a product by omega) hr
  have hhi := Int.mul_le_mul_of_nonneg_right (show Z.rem a product ≤ 46340 by omega) hr
  omega

theorem crt_fold_product_app__crt_transition (l1 l2 : List Int) :
    (l1++l2).foldr (· * ·) 1 = l1.foldr (· * ·) 1 * l2.foldr (· * ·) 1 :=
  crt_product_app__product_progress l1 l2

theorem crt_gcd_of_bezout_one__crt_transition (a b : Int) (h : Z.Bezout a b 1) : Z.gcd a b = 1 := by
  obtain ⟨x, y, he⟩ := h
  have hg : Int.gcd a b = 1 := by
    apply Int.gcd_eq_one_iff.mpr
    intro c ha hb
    obtain ⟨qa, hqa⟩ := ha
    obtain ⟨qb, hqb⟩ := hb
    exact ⟨x*qa+y*qb, by grind⟩
  simp [Z.gcd, hg]

theorem crt_gcd_mul_one__crt_transition (a b m : Int) (ha : Z.gcd a m = 1) (hb : Z.gcd b m = 1) :
    Z.gcd (a*b) m = 1 := by
  have hna : Int.gcd a m = 1 := by exact Int.ofNat_inj.mp ha
  have hnb : Int.gcd b m = 1 := by exact Int.ofNat_inj.mp hb
  simp [Z.gcd, Int.gcd_mul_right_left_of_gcd_eq_one hna, hnb]

theorem crt_fold_product_coprime__crt_transition (l : List Int) (m : Int)
    (ha : ∀ k, (0 ≤ k ∧ k < Zlength l) → Z.gcd (Znth k l 0) m = 1) :
    Z.gcd (l.foldr (· * ·) 1) m = 1 := by
  induction l with
  | nil => simp [Z.gcd]
  | cons a l ih =>
    apply crt_gcd_mul_one__crt_transition
    · have h := ha 0 (by rw [Zlength_cons]; have := Zlength_nonneg l; omega)
      simpa using h
    · apply ih
      intro k hk
      have h := ha (k+1) (by rw [Zlength_cons]; omega)
      rw [Znth_cons 0 (k+1) a l (by omega), show k+1-1 = k by omega] at h
      exact h

theorem crt_Znth_divides_fold_product__crt_transition (l : List Int) (k : Int)
    (hk : 0 ≤ k ∧ k < Zlength l) : Z.divide (Znth k l 0) (l.foldr (· * ·) 1) := index_divides l k hk

private theorem sublist_Zlength (lo hi : Int) (l : List Int)
    (hl : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l) : Zlength (sublist lo hi l) = hi-lo := by
  unfold Zlength
  rw [sublist_length lo hi l hl hh]
  simp only [Int.ofNat_eq_coe]
  omega

theorem crt_product_factor_arithmetic__crt_transition (remainders moduli : List Int) (i : Int)
    (hv : CRTInputValid remainders moduli) (hi : 0 ≤ i ∧ i < Zlength moduli) :
    let m := Znth i moduli 0
    let q := Z.div (CRTProduct moduli) m
    q*m = CRTProduct moduli ∧ Z.gcd q m = 1 ∧
    ∀ j, (0 ≤ j ∧ j < Zlength moduli) → j ≠ i → Z.divide (Znth j moduli 0) q := by
  dsimp only
  let pre := sublist 0 i moduli
  let suf := sublist (i+1) (Zlength moduli) moduli
  have hpre : Zlength pre = i := by change Zlength (sublist 0 i moduli) = i; rw [sublist_Zlength 0 i moduli (by omega) (by omega)]; omega
  have hsuf : Zlength suf = Zlength moduli-(i+1) := sublist_Zlength (i+1) (Zlength moduli) moduli (by omega) (by omega)
  have hdec : moduli = pre ++ [Znth i moduli 0] ++ suf := by
    have hwhole := sublist_split 0 (Zlength moduli) i moduli (by omega) (by omega)
    rw [sublist_self moduli (Zlength moduli) rfl,
      sublist_split i (Zlength moduli) (i+1) moduli (by omega) (by omega), sublist_single 0 i moduli hi] at hwhole
    simpa only [List.append_assoc, pre, suf] using hwhole
  have hprod : CRTProduct moduli = (CRTProduct pre * CRTProduct suf) * Znth i moduli 0 := by
    conv => lhs; rw [hdec]
    rw [crt_product_app__product_progress, crt_product_app__product_progress]
    simp only [CRTProduct, List.foldr_cons, List.foldr_nil, Int.mul_one]
    grind
  have hm := (hv.2.2.1 i hi).1
  have hq : Z.div (CRTProduct moduli) (Znth i moduli 0) = CRTProduct pre * CRTProduct suf := by
    rw [hprod]
    exact Int.mul_fdiv_cancel _ (by omega)
  rw [hq]
  refine ⟨hprod.symm, ?_, ?_⟩
  · apply crt_gcd_mul_one__crt_transition
    · apply crt_fold_product_coprime__crt_transition
      intro k hk
      have h := hv.2.2.2 k i (by omega)
      rw [show Znth k pre 0 = Znth k moduli 0 by
        dsimp [pre]; rw [Znth_sublist 0 0 k i moduli (by omega) (by omega)]; simp]
      exact h
    · apply crt_fold_product_coprime__crt_transition
      intro k hk
      have h := hv.2.2.2 i (k+(i+1)) (by omega)
      rw [show Znth k suf 0 = Znth (k+(i+1)) moduli 0 by
        exact Znth_sublist 0 (i+1) k (Zlength moduli) moduli (by omega) (by omega)]
      rw [Z.gcd_comm]
      exact h
  · intro j hj hji
    by_cases hlt : j < i
    · obtain ⟨q, hq⟩ := index_divides pre j (by omega)
      have he : Znth j pre 0 = Znth j moduli 0 := by
        dsimp [pre]; rw [Znth_sublist 0 0 j i moduli (by omega) (by omega)]; simp
      rw [he] at hq
      exact ⟨q * CRTProduct suf, by change CRTProduct pre = _ at hq; rw [hq]; grind⟩
    · obtain ⟨q, hq⟩ := index_divides suf (j-(i+1)) (by omega)
      have he : Znth (j-(i+1)) suf 0 = Znth j moduli 0 := by
        change Znth (j-(i+1)) (sublist (i+1) (Zlength moduli) moduli) 0 = Znth j moduli 0
        rw [Znth_sublist 0 (i+1) (j-(i+1)) (Zlength moduli) moduli (by omega) (by omega)]
        congr 1; omega
      rw [he] at hq
      exact ⟨CRTProduct pre*q, by change CRTProduct suf = _ at hq; rw [hq]; grind⟩

private theorem mod_mod_dvd (a p m : Int) (hp : 0 ≤ p) (hm : 0 ≤ m) (hd : Z.divide m p) :
    Z.modulo (Z.modulo a p) m = Z.modulo a m := by
  unfold Z.modulo
  rw [Int.fmod_eq_emod_of_nonneg a hp, Int.fmod_eq_emod_of_nonneg _ hm, Int.fmod_eq_emod_of_nonneg _ hm]
  exact Int.emod_emod_of_dvd a ((Z.divide_iff_dvd _ _).mp hd)

theorem crt_update_processed__crt_transition (remainders moduli : List Int) (result i product x y : Int)
    (hv : CRTInputValid remainders moduli) (hi : 0 ≤ i ∧ i < Zlength moduli)
    (hp : product = CRTProduct moduli) (hpp : 1 ≤ product)
    (hc : CRTProcessedCongruences remainders moduli i result)
    (hz : ∀ k, (i ≤ k ∧ k < Zlength moduli) → Z.modulo result (Znth k moduli 0) = 0)
    (hb : Z.div product (Znth i moduli 0)*x + Znth i moduli 0*y = Z.gcd (Z.div product (Znth i moduli 0)) (Znth i moduli 0)) :
    CRTProcessedCongruences remainders moduli (i+1)
      (Z.modulo (result + Z.modulo (Z.modulo (x * Z.div product (Znth i moduli 0)) product * Znth i remainders 0) product) product) := by
  have hf := crt_product_factor_arithmetic__crt_transition remainders moduli i hv hi
  dsimp only at hf
  rw [← hp] at hf
  let m := Znth i moduli 0
  let q := Z.div product m
  let r := Znth i remainders 0
  change q*m = product ∧ Z.gcd q m = 1 ∧ _ at hf
  change q*x+m*y = Z.gcd q m at hb
  rw [hf.2.1] at hb
  have hmr := hv.2.2.1 i hi
  change 1 ≤ m ∧ 0 ≤ r ∧ r < m at hmr
  change CRTProcessedCongruences remainders moduli (i+1) (Z.modulo (result + Z.modulo (Z.modulo (x*q) product * r) product) product)
  intro j hj
  have hjr : 0 ≤ j ∧ j < Zlength moduli := by omega
  have hmj := (hv.2.2.1 j hjr).1
  have hd : Z.divide (Znth j moduli 0) product := by rw [hp]; exact index_divides moduli j hjr
  rw [mod_mod_dvd _ product _ (by omega) (by omega) hd]
  by_cases hji : j < i
  · obtain ⟨f, hfact⟩ := hf.2.2 j hjr (by omega)
    change q = f * Znth j moduli 0 at hfact
    have hcoef : Z.modulo (Z.modulo (x*q) product) (Znth j moduli 0) = 0 := by
      rw [mod_mod_dvd _ product _ (by omega) (by omega) hd, hfact]
      change Int.fmod (x*(f*Znth j moduli 0)) (Znth j moduli 0) = 0
      rw [← Int.mul_assoc, Int.mul_fmod_left]
    have ht : Z.modulo (Z.modulo (Z.modulo (x*q) product*r) product) (Znth j moduli 0) = 0 := by
      rw [mod_mod_dvd _ product _ (by omega) (by omega) hd]
      change Int.fmod (Z.modulo (x*q) product*r) (Znth j moduli 0) = 0
      rw [Int.mul_fmod, show Int.fmod (Z.modulo (x*q) product) (Znth j moduli 0) = 0 from hcoef]
      simp
    change Int.fmod (result+_) (Znth j moduli 0) = _
    rw [Int.add_fmod, show Int.fmod result (Znth j moduli 0) = Znth j remainders 0 from hc j (by omega),
      show Int.fmod (Z.modulo (Z.modulo (x*q) product*r) product) (Znth j moduli 0) = 0 from ht, Int.add_zero]
    exact Int.fmod_eq_of_lt (hv.2.2.1 j hjr).2.1 (hv.2.2.1 j hjr).2.2
  · have he : j = i := by omega
    subst j
    have hzero := hz i (by omega)
    change Z.modulo result m = 0 at hzero
    change Z.divide m product at hd
    have hcoef : Z.modulo (Z.modulo (x*q) product) m = Z.modulo 1 m := by
      rw [mod_mod_dvd _ product m (by omega) (by omega) hd]
      have he : x*q = 1+(-y)*m := by grind
      rw [he]
      exact Int.add_mul_fmod_self_right 1 (-y) m
    have ht : Z.modulo (Z.modulo (Z.modulo (x*q) product*r) product) m = r := by
      rw [mod_mod_dvd _ product m (by omega) (by omega) hd]
      change Int.fmod (Z.modulo (x*q) product*r) m = r
      rw [Int.mul_fmod, show Int.fmod (Z.modulo (x*q) product) m = Int.fmod 1 m from hcoef,
        ← Int.mul_fmod, Int.one_mul]
      exact Int.fmod_eq_of_lt hmr.2.1 hmr.2.2
    change Int.fmod (result+_) m = r
    rw [Int.add_fmod, show Int.fmod result m = 0 from hzero,
      show Int.fmod (Z.modulo (Z.modulo (x*q) product*r) product) m = r from ht, Int.zero_add]
    exact Int.fmod_eq_of_lt hmr.2.1 hmr.2.2

theorem crt_rem_mod__crt_transition (a p : Int) (hp : p ≠ 0) : Z.modulo (Z.rem a p) p = Z.modulo a p := by
  have he := Int.tmod_add_tdiv_mul a p
  calc
    Z.modulo (Z.rem a p) p = Z.modulo (Z.rem a p + Z.quot a p*p) p := (Int.add_mul_fmod_self_right _ _ _).symm
    _ = Z.modulo a p := congrArg (fun n => Z.modulo n p) he

theorem crt_rem_mul_mod__crt_transition (a r p : Int) (hp : p ≠ 0) :
    Z.modulo (Z.rem a p*r) p = Z.modulo (Z.modulo a p*r) p := by
  change Int.fmod (Z.rem a p*r) p = Int.fmod (Z.modulo a p*r) p
  rw [Int.mul_fmod, show Int.fmod (Z.rem a p) p = Int.fmod a p from crt_rem_mod__crt_transition a p hp,
    show Z.modulo a p = Int.fmod a p from rfl]
  simpa using (Int.mul_fmod (Int.fmod a p) r p).symm

theorem crt_nonnegative_rem_eq_mod__crt_transition (a p : Int) (hp : 0 < p) (hr : 0 ≤ Z.rem a p) :
    Z.rem a p = Z.modulo a p := by
  have hb := AUXLib.rem_bounds a p hp
  have hs : Z.modulo (Z.rem a p) p = Z.rem a p := Int.fmod_eq_of_lt hr hb.2
  rw [← hs]
  exact crt_rem_mod__crt_transition a p (by omega)

theorem crt_quot_div_pos__crt_transition (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : Z.quot a b = Z.div a b := by
  exact (Int.fdiv_eq_tdiv_of_nonneg ha hb).symm

theorem crt_rem_eq_mod_of_nonnegative_dividend__crt_transition (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
    Z.rem a b = Z.modulo a b := AUXLib.rem_eq_mod a b ha hb

end SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_lib
namespace SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem
export chinese_remainder_theorem_lib (CRTProduct CRTInputValid CRTMachineSafe CanonicalCRTSolution CRTProcessedCongruences)
end SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_lib
open AUXLib

def CRTConsistentPrefix (remainders moduli : List Int) (processed result : Int) : Prop :=
  Forall2 (fun remainder modulus => Z.modulo result modulus = remainder)
    (sublist 0 processed remainders) (sublist 0 processed moduli)
def CRTUnprocessedZero (moduli : List Int) (processed result : Int) : Prop :=
  Forall (fun modulus => Z.rem result modulus = 0) (sublist processed (Zlength moduli) moduli)

end SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_lib
namespace SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem
export chinese_remainder_theorem_lib (CRTConsistentPrefix CRTUnprocessedZero)
end SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem
