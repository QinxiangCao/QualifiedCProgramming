import AUXLib.Prime
import AUXLib.ListLib.Base

set_option maxHeartbeats 6000000
set_option maxRecDepth 6000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_lib
open AUXLib AUXLib.Prime

-- Reached Coq 8.20.1 Arith/Factorial.v:16, with the same recursion equations.
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*fact n

def ModularPower (base exponent modulus result : Int) : Prop := result=Z.modulo (Z.pow base exponent) modulus

def PrimeForLucas (p : Int) : Prop :=
  2≤p ∧ ∀ divisor : Int, 2≤divisor ∧ divisor<p → Z.modulo p divisor≠0

def LucasNatBinomial : Nat → Nat → Nat
  | _,0 => 1
  | 0,_+1 => 0
  | n+1,k+1 => LucasNatBinomial n k+LucasNatBinomial n (k+1)

def LucasBinomialCoefficient (upper lower : Int) : Int := Int.ofNat (LucasNatBinomial upper.toNat lower.toNat)

def BinomialDigitResidue (upper lower p result : Int) : Prop := result=Z.modulo (LucasBinomialCoefficient upper lower) p

def LucasBinomialResidue (n m p result : Int) : Prop := result=Z.modulo (LucasBinomialCoefficient (n+m) n) p

def DigitEffectiveLower (upper lower : Int) : Int := min lower (upper-lower)

def LucasRangeProduct (start count : Int) : Int :=
  ((List.range' 0 count.toNat).map (fun offset : Nat => start+Int.ofNat offset)).foldr (· * ·) 1

def DigitNumeratorPrefix (upper lower processed : Int) : Int := LucasRangeProduct (upper-lower+1) processed

def DigitDenominatorPrefix (processed : Int) : Int := LucasRangeProduct 1 processed

def DigitBinomialMachineSafe (upper original_lower p : Int) : Prop :=
  let lower := DigitEffectiveLower upper original_lower
  (∀ next : Int,1≤next ∧ next≤lower →
    (0≤Z.modulo (DigitNumeratorPrefix upper lower (next-1)) p*(upper-lower+next) ∧
      Z.modulo (DigitNumeratorPrefix upper lower (next-1)) p*(upper-lower+next)≤2147483647) ∧
    (0≤Z.modulo (DigitDenominatorPrefix (next-1)) p*next ∧ Z.modulo (DigitDenominatorPrefix (next-1)) p*next≤2147483647)) ∧
  (∀ inverse : Int,ModularPower (Z.modulo (DigitDenominatorPrefix lower) p) (p-2) p inverse →
    0≤Z.modulo (DigitNumeratorPrefix upper lower lower) p*inverse ∧ Z.modulo (DigitNumeratorPrefix upper lower lower) p*inverse≤2147483647)

def LucasDigit (value p : Int) (position : Nat) : Int := Z.modulo (Z.div value (Z.pow p (Int.ofNat position))) p

def LucasPrefixProduct (upper lower p : Int) (digits : Nat) : Int :=
  Z.modulo (((List.range' 0 digits).map (fun position => Z.modulo (LucasBinomialCoefficient (LucasDigit upper p position) (LucasDigit lower p position)) p)).foldr (· * ·) 1) p

def LucasMachineSafe (n m p : Int) : Prop :=
  ∀ processed : Nat,
    let upper_digit := LucasDigit (n+m) p processed
    let lower_digit := LucasDigit n p processed
    lower_digit≤upper_digit → DigitBinomialMachineSafe upper_digit lower_digit p ∧
    (0≤LucasPrefixProduct (n+m) n p processed*Z.modulo (LucasBinomialCoefficient upper_digit lower_digit) p ∧
      LucasPrefixProduct (n+m) n p processed*Z.modulo (LucasBinomialCoefficient upper_digit lower_digit) p≤2147483647)

def DigitProductProgress (upper lower p next numerator denominator : Int) : Prop :=
  numerator=Z.modulo (DigitNumeratorPrefix upper lower (next-1)) p ∧ denominator=Z.modulo (DigitDenominatorPrefix (next-1)) p

def LucasProgress (original_upper original_lower p current_upper current_lower result : Int) : Prop :=
  ∃ processed : Nat,current_upper=Z.div original_upper (Z.pow p (Int.ofNat processed)) ∧
    current_lower=Z.div original_lower (Z.pow p (Int.ofNat processed)) ∧ result=LucasPrefixProduct original_upper original_lower p processed ∧
    Z.modulo (LucasBinomialCoefficient original_upper original_lower) p=Z.modulo (result*LucasBinomialCoefficient current_upper current_lower) p

private theorem zpow_nat (a e : Int) (he : 0≤e) : Z.pow a e=a^e.toNat := by
  cases e <;> simp_all [Z.pow]


private theorem zpow_succ (a e : Int) (he : 0≤e) : Z.pow a (e+1)=Z.pow a e*a := by
  cases e with
  | ofNat e => exact Int.pow_succ a e
  | negSucc e => omega


private theorem zpow_pos (a e : Int) (ha : 0<a) (he : 0≤e) : 0<Z.pow a e := by
  rw [zpow_nat a e he]
  exact Int.pow_pos ha


private theorem zpow_split (a e : Int) (he : 1≤e) : Z.pow a e=a*Z.pow a (e-1) := by
  have h := zpow_succ a (e-1) (by omega)
  simpa [Int.mul_comm] using h


private theorem gcd_fmod (a n : Int) : Int.gcd (a.fmod n) n=Int.gcd a n := by
  have h := Int.fmod_add_mul_fdiv a n
  calc
    _ = Int.gcd (a.fmod n+n*a.fdiv n) n := (Int.gcd_add_mul_left_left n (a.fmod n) (a.fdiv n)).symm
    _ = Int.gcd a n := by rw [h]


private theorem gcd1_mod_nonzero (x n : Int) (hn : 2≤n) (hg : Int.gcd x n=1) : x.fmod n≠0 := by
  intro h0
  have h := gcd_fmod x n
  rw [h0,Int.zero_gcd,hg] at h
  have habs : (n.natAbs : Int)=n := (Int.eq_natAbs_of_nonneg (by omega)).symm
  omega


private theorem gcd1_prime (p x : Int) (hp : prime p) (hn : ¬p∣x) : Int.gcd x p=1 := by
  have hp2 := prime_ge_2 p hp
  have hdiv := Int.gcd_dvd_right x p
  have hdx := Int.gcd_dvd_left x p
  have hgpos := Int.gcd_pos_of_ne_zero_right x (by omega : p≠0)
  rcases prime_divisors p hp (Int.gcd x p) ((Z.divide_iff_dvd _ _).2 hdiv) with h | h | h | h
  · omega
  · omega
  · exact False.elim (hn (h ▸ hdx))
  · omega


private theorem nodup_map_on {A B : Type} (f : A→B) (l : List A) (hl : l.Nodup)
    (hinj : ∀ x, x∈l → ∀ y,y∈l → f x=f y → x=y) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    have ha := List.nodup_cons.mp hl
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_map.mp hm with ⟨x,hx,hxa⟩
      exact ha.1 (hinj x (by simp [hx]) a (by simp) hxa ▸ hx)
    · exact ih ha.2 (by intro x hx y hy he; exact hinj x (by simp [hx]) y (by simp [hy]) he)


private theorem nodup_perm {A : Type} [DecidableEq A] (l1 l2 : List A)
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hm : ∀ x,x∈l1 ↔ x∈l2) : l1.Perm l2 := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [h1.count,h2.count,hm x]


private theorem perm_of_nodup_subset_length {A : Type} [DecidableEq A] (l1 l2 : List A)
    (hnd : l1.Nodup) (hlen : l1.length=l2.length) (hsub : ∀ x,x∈l1 → x∈l2) : l1.Perm l2 := by
  induction l1 generalizing l2 with
  | nil => have he : l2=[] := List.length_eq_zero_iff.mp hlen.symm; subst l2; exact List.Perm.refl []
  | cons a l ih =>
    have ha := List.nodup_cons.mp hnd
    have ham := hsub a (by simp)
    apply List.cons_perm_iff_perm_erase.mpr
    refine ⟨ham,ih (l2.erase a) ha.2 ?_ ?_⟩
    · rw [List.length_erase_of_mem ham]
      simp only [List.length_cons] at hlen
      omega
    · intro x hx
      have hxa : x≠a := by intro he; subst x; exact ha.1 hx
      exact (List.mem_erase_of_ne hxa).mpr (hsub x (by simp [hx]))


private theorem mod_eq_of_dvd_sub (x y n : Int) (hd : n∣x-y) : x.fmod n=y.fmod n :=
  Int.fmod_eq_fmod_iff_fmod_sub_eq_zero.mpr (Int.fmod_eq_zero_of_dvd hd)


private theorem eq_of_dvd_sub_bounds (x y n : Int) (hx : 0≤x ∧ x<n) (hy : 0≤y ∧ y<n)
    (hd : n∣x-y) : x=y := by
  have h := mod_eq_of_dvd_sub x y n hd
  rw [Int.fmod_eq_of_lt hx.1 hx.2,Int.fmod_eq_of_lt hy.1 hy.2] at h
  exact h


private theorem dvd_sub_of_mod_eq (x y n : Int) (he : x.fmod n=y.fmod n) : n∣x-y :=
  Int.dvd_of_fmod_eq_zero (Int.fmod_eq_fmod_iff_fmod_sub_eq_zero.mp he)


private theorem coprime_cancel_dvd (n a x : Int) (hg : Int.gcd n a=1) (hd : n∣a*x) : n∣x := by
  have ht := (Int.dvd_gcd_mul_iff_dvd_mul (k:=n) (n:=a) (m:=x)).2 hd
  simpa [hg] using ht


private theorem zprod_append (l1 l2 : List Int) :
    (l1++l2).foldr (· * ·) 1=l1.foldr (· * ·) 1*l2.foldr (· * ·) 1 := by
  induction l1 with
  | nil => simp
  | cons a l ih => simp only [List.cons_append,List.foldr_cons,ih]; grind

private theorem nprod_append (l1 l2 : List Nat) :
    (l1++l2).foldr (· * ·) 1=l1.foldr (· * ·) 1*l2.foldr (· * ·) 1 := by
  induction l1 with
  | nil => simp
  | cons a l ih => simp only [List.cons_append,List.foldr_cons,ih]; grind

private theorem factorial_pos (n : Nat) : 0<fact n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem lucas_range_product_zero__digit_product_progress (start : Int) : LucasRangeProduct start 0=1 := rfl

theorem lucas_range_product_succ__digit_product_progress (start count : Int) : 0≤count →
    LucasRangeProduct start (count+1)=LucasRangeProduct start count*(start+count) := by
  intro hc
  have hnat : (count+1).toNat=count.toNat+1 := by omega
  unfold LucasRangeProduct
  rw [hnat,List.range'_1_concat,List.map_append,zprod_append]
  simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,Int.mul_one,Nat.zero_add]
  have he : (Int.ofNat count.toNat)=count := by simp only [Int.ofNat_eq_coe]; omega
  rw [he]

theorem digit_product_progress_step__digit_product_progress (upper lower p next numerator denominator : Int) :
    p≠0 → 1≤next → DigitProductProgress upper lower p next numerator denominator →
    DigitProductProgress upper lower p (next+1) (Z.modulo (numerator*(upper-lower+next)) p) (Z.modulo (denominator*next) p) := by
  rintro hp hn ⟨hnum,hden⟩
  unfold DigitProductProgress DigitNumeratorPrefix DigitDenominatorPrefix at *
  have h1 := lucas_range_product_succ__digit_product_progress (upper-lower+1) (next-1) (by omega)
  have h2 := lucas_range_product_succ__digit_product_progress 1 (next-1) (by omega)
  simp only [Int.sub_add_cancel,Int.add_sub_cancel] at h1 h2 ⊢
  have he1 : upper-lower+1+(next-1)=upper-lower+next := by omega
  have he2 : 1+(next-1)=next := by omega
  rw [he1] at h1
  rw [he2] at h2
  rw [hnum,hden,h1,h2]
  unfold Z.modulo
  constructor <;> rw [Int.mul_fmod,Int.fmod_fmod,←Int.mul_fmod]

theorem prime_for_lucas_prime__digit_final_residue (p : Int) : PrimeForLucas p → prime p := by
  rintro ⟨hp,hdiv⟩
  apply (prime_alt p).1
  refine ⟨by omega,?_⟩
  intro d hd hpd
  exact hdiv d ⟨by omega,hd.2⟩ (Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).1 hpd))

theorem lucas_nat_binomial_zero__digit_final_residue (n : Nat) : LucasNatBinomial n 0=1 := by cases n <;> rfl

theorem lucas_nat_binomial_one__digit_final_residue (n : Nat) : LucasNatBinomial n 1=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [LucasNatBinomial,lucas_nat_binomial_zero__digit_final_residue,ih]; omega

theorem lucas_nat_binomial_above__digit_final_residue (n k : Nat) : n<k → LucasNatBinomial n k=0 := by
  intro hn
  induction n generalizing k with
  | zero => cases k <;> simp_all [LucasNatBinomial]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => rw [LucasNatBinomial,ih k (by omega),ih (k+1) (by omega)]

theorem lucas_nat_binomial_diagonal__digit_final_residue (n : Nat) : LucasNatBinomial n n=1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [LucasNatBinomial,ih,lucas_nat_binomial_above__digit_final_residue n (n+1) (by omega)]

private theorem binomial_factorial (n k : Nat) (hk : k≤n) :
    LucasNatBinomial n k*fact k*fact (n-k)=fact n := by
  induction n generalizing k with
  | zero =>
    have he : k=0 := by omega
    subst k
    rfl
  | succ n ih =>
    cases k with
    | zero => simp [lucas_nat_binomial_zero__digit_final_residue,fact]
    | succ k =>
      by_cases he : k=n
      · subst k
        rw [lucas_nat_binomial_diagonal__digit_final_residue]
        simp [fact]
      · have hk' : k<n := by omega
        have ih1 := ih k (by omega)
        have ih2 := ih (k+1) (by omega)
        have he1 : n+1-(k+1)=n-k := by omega
        have he2 : n-k=(n-(k+1))+1 := by omega
        rw [LucasNatBinomial,he1]
        rw [he2,fact] at ih1 ⊢
        simp only [fact] at ih2 ⊢
        have hkval : k+1+(n-(k+1)+1)=n+1 := by omega
        grind

theorem lucas_nat_binomial_symmetry__digit_final_residue (n k : Nat) : k≤n → LucasNatBinomial n k=LucasNatBinomial n (n-k) := by
  intro hk
  have h1 := binomial_factorial n k hk
  have h2 := binomial_factorial n (n-k) (by omega)
  have hn : n-(n-k)=k := by omega
  rw [hn] at h2
  apply Nat.eq_of_mul_eq_mul_right (m:=fact k*fact (n-k)) (Nat.mul_pos (factorial_pos k) (factorial_pos (n-k)))
  grind

theorem lucas_binomial_symmetry_z__digit_final_residue (upper lower : Int) :
    (0≤lower ∧ lower≤upper) → LucasBinomialCoefficient upper lower=LucasBinomialCoefficient upper (upper-lower) := by
  intro hr
  unfold LucasBinomialCoefficient
  have he : (upper-lower).toNat=upper.toNat-lower.toNat := by omega
  rw [he,lucas_nat_binomial_symmetry__digit_final_residue upper.toNat lower.toNat (by omega)]

theorem lucas_nat_binomial_step__digit_final_residue (n k : Nat) : k<n →
    LucasNatBinomial n (k+1)*(k+1)=LucasNatBinomial n k*(n-k) := by
  intro hk
  have h1 := binomial_factorial n k (by omega)
  have h2 := binomial_factorial n (k+1) (by omega)
  have hdiff : n-k=(n-(k+1))+1 := by omega
  rw [hdiff,fact] at h1
  simp only [fact] at h2
  apply Nat.eq_of_mul_eq_mul_right (m:=fact k*fact (n-(k+1))) (Nat.mul_pos (factorial_pos k) (factorial_pos (n-(k+1))))
  rw [hdiff]
  grind

theorem fold_right_Zmul_snoc__digit_final_residue (l : List Int) (x : Int) :
    (l++[x]).foldr (· * ·) 1=l.foldr (· * ·) 1*x := by
  rw [zprod_append]
  simp

theorem lucas_range_product_succ_end__digit_final_residue (start : Int) (count : Nat) :
    LucasRangeProduct start (Int.ofNat (count+1))=LucasRangeProduct start (Int.ofNat count)*(start+Int.ofNat count) := by
  have h := lucas_range_product_succ__digit_product_progress start (Int.ofNat count) (by simp only [Int.ofNat_eq_coe]; omega)
  exact h

theorem lucas_range_product_succ_start__digit_final_residue (start : Int) (count : Nat) :
    LucasRangeProduct start (Int.ofNat (count+1))=start*LucasRangeProduct (start+1) (Int.ofNat count) := by
  unfold LucasRangeProduct
  simp only [Int.ofNat_eq_coe,Int.toNat_natCast,List.range'_succ,List.map_cons,List.foldr_cons]
  have he : (List.range' 1 count).map (fun offset => start+Int.ofNat offset)=
      (List.range' 0 count).map (fun offset => (start+1)+Int.ofNat offset) := by
    rw [List.range'_succ_left,List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply,Int.ofNat_eq_coe,Int.natCast_add,Int.natCast_one]
    omega
  simp only [Int.ofNat_eq_coe] at he
  rw [he]
  simp

theorem lucas_nat_binomial_range_product__digit_final_residue (n k : Nat) : k≤n →
    Int.ofNat (LucasNatBinomial n k)*LucasRangeProduct 1 (Int.ofNat k)=LucasRangeProduct (Int.ofNat (n-k)+1) (Int.ofNat k) := by
  intro hk
  induction k with
  | zero => simp [lucas_nat_binomial_zero__digit_final_residue,LucasRangeProduct]
  | succ k ih =>
    have hstep := congrArg Int.ofNat (lucas_nat_binomial_step__digit_final_residue n k (by omega))
    simp only [Int.ofNat_eq_coe,Int.natCast_mul] at hstep
    have hi := ih (by omega)
    have he : Int.ofNat (n-(k+1))+1=Int.ofNat (n-k) := by simp only [Int.ofNat_eq_coe]; omega
    rw [lucas_range_product_succ_end__digit_final_residue,he,lucas_range_product_succ_start__digit_final_residue]
    have he' : (1:Int)+Int.ofNat k=Int.ofNat (k+1) := by simp only [Int.ofNat_eq_coe]; omega
    rw [he']
    grind

theorem lucas_binomial_range_product_z__digit_final_residue (upper lower : Int) :
    (0≤lower ∧ lower≤upper) → LucasBinomialCoefficient upper lower*DigitDenominatorPrefix lower=DigitNumeratorPrefix upper lower lower := by
  intro h
  have hp := lucas_nat_binomial_range_product__digit_final_residue upper.toNat lower.toNat (by omega)
  have hl : Int.ofNat lower.toNat=lower := by simp only [Int.ofNat_eq_coe]; omega
  have hdiff : Int.ofNat (upper.toNat-lower.toNat)=upper-lower := by simp only [Int.ofNat_eq_coe]; omega
  rw [hl,hdiff] at hp
  exact hp

theorem prime_product_not_divisible__digit_final_residue (p : Int) (l : List Int) :
    prime p → Forall (fun x => 1≤x ∧ x<p) l → ¬Z.divide p (l.foldr (· * ·) 1) := by
  intro hp hl
  have hp2 := prime_ge_2 p hp
  induction l with
  | nil =>
    intro hd
    have hle := Int.le_of_dvd (by omega : (0:Int)<1) ((Z.divide_iff_dvd _ _).1 hd)
    omega
  | cons x l ih =>
    cases hl with
    | cons hx hl =>
      intro hd
      rcases prime_mult p hp x (l.foldr (· * ·) 1) hd with hd | hd
      · have hle := Int.le_of_dvd (by omega : 0<x) ((Z.divide_iff_dvd _ _).1 hd)
        omega
      · exact ih hl hd

theorem digit_factorial_nonzero_mod_prime__digit_final_residue (lower p : Int) :
    (0≤lower ∧ lower<p) → PrimeForLucas p → Z.modulo (DigitDenominatorPrefix lower) p≠0 := by
  intro hl hp hm
  apply prime_product_not_divisible__digit_final_residue p _ (prime_for_lucas_prime__digit_final_residue p hp) _ ((Z.divide_iff_dvd _ _).2 (Int.dvd_of_fmod_eq_zero hm))
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_map.mp hx with ⟨i,hi,he⟩
  rcases List.mem_range'.mp hi with ⟨j,hj,hij⟩
  simp only [Nat.zero_add,Nat.one_mul] at hij
  subst i
  simp only [Int.ofNat_eq_coe] at he
  omega

theorem NoDup_map_Zof_nat_seq__digit_final_residue (start len : Nat) :
    ((List.range' start len).map Int.ofNat).Nodup := by
  apply nodup_map_on _ _ (List.nodup_range' _)
  intro x hx y hy he
  exact Int.ofNat_inj.mp he

theorem in_lucas_residues__digit_final_residue (p x : Int) : 1<p →
    (x∈((List.range' 1 (p-1).toNat).map Int.ofNat) ↔ (1≤x ∧ x<p)) := by
  intro hp
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨i,hi,he⟩
    rcases List.mem_range'.mp hi with ⟨j,hj,hij⟩
    simp only [Int.ofNat_eq_coe] at he
    omega
  · intro hx
    apply List.mem_map.mpr
    refine ⟨x.toNat,?_,by simp only [Int.ofNat_eq_coe]; omega⟩
    apply List.mem_range'.mpr
    exact ⟨x.toNat-1,by omega,by omega⟩

theorem prime_mul_mod_cancel__digit_final_residue (p a x y : Int) :
    prime p → (0<a ∧ a<p) → (1≤x ∧ x<p) → (1≤y ∧ y<p) → Z.modulo (a*x) p=Z.modulo (a*y) p → x=y := by
  intro hp ha hx hy he
  have hnp : ¬p∣a := by
    intro hd
    have hle := Int.le_of_dvd ha.1 hd
    omega
  have hga := gcd1_prime p a hp hnp
  have hg : Int.gcd p a=1 := by rw [Int.gcd_comm]; exact hga
  have hd := dvd_sub_of_mod_eq _ _ _ he
  have hdm : p∣a*(x-y) := by
    have h : a*(x-y)=a*x-a*y := by grind
    rw [h]; exact hd
  exact eq_of_dvd_sub_bounds x y p ⟨by omega,hx.2⟩ ⟨by omega,hy.2⟩ (coprime_cancel_dvd p a (x-y) hg hdm)

theorem prime_mul_residue_in_lucas_residues__digit_final_residue (p a x : Int) :
    prime p → (0<a ∧ a<p) → x∈((List.range' 1 (p-1).toNat).map Int.ofNat) →
    Z.modulo (a*x) p∈((List.range' 1 (p-1).toNat).map Int.ofNat) := by
  intro hp ha hx
  have hp2 := prime_ge_2 p hp
  have hr := (in_lucas_residues__digit_final_residue p x (by omega)).1 hx
  have ga := gcd1_prime p a hp (by intro hd; have := Int.le_of_dvd ha.1 hd; omega)
  have gx := gcd1_prime p x hp (by intro hd; have := Int.le_of_dvd (by omega : 0<x) hd; omega)
  have gax : Int.gcd (a*x) p=1 := by rw [Int.gcd_mul_right_left_of_gcd_eq_one ga]; exact gx
  have hn := gcd1_mod_nonzero (a*x) p hp2 gax
  have h0 := Int.fmod_nonneg_of_pos (a*x) (by omega : 0<p)
  have hlt := Int.fmod_lt_of_pos (a*x) (by omega : 0<p)
  exact (in_lucas_residues__digit_final_residue p _ (by omega)).2 ⟨by unfold Z.modulo; omega,hlt⟩

theorem prime_mul_residue_preimage__digit_final_residue (p a z : Int) :
    prime p → (0<a ∧ a<p) → z∈((List.range' 1 (p-1).toNat).map Int.ofNat) →
    ∃ x : Int,Z.modulo (a*x) p=z ∧ x∈((List.range' 1 (p-1).toNat).map Int.ofNat) := by
  intro hp ha hz
  have hp2 := prime_ge_2 p hp
  have ga := gcd1_prime p a hp (by intro hd; have := Int.le_of_dvd ha.1 hd; omega)
  rcases AUXLib.RelPrime.gcd_eq_one_bezout a p (congrArg Int.ofNat ga) with ⟨u,v,huv⟩
  let x := Z.modulo (u*z) p
  have hzrange := (in_lucas_residues__digit_final_residue p z (by omega)).1 hz
  have he : Z.modulo (a*x) p=z := by
    have hprod : a*(u*z)=z+p*(-v*z) := by grind
    change (a*(u*z).fmod p).fmod p=z
    rw [Int.mul_fmod,Int.fmod_fmod,←Int.mul_fmod,hprod,Int.add_mul_fmod_self_left]
    exact Int.fmod_eq_of_lt (by omega) hzrange.2
  have hx0 : 0≤x := Int.fmod_nonneg_of_pos _ (by omega)
  have hxlt : x<p := Int.fmod_lt_of_pos _ (by omega)
  have hxpos : 0<x := by
    by_cases h : x=0
    · rw [h] at he
      simp only [Int.mul_zero,Z.modulo,Int.zero_fmod] at he
      omega
    · omega
  exact ⟨x,he,(in_lucas_residues__digit_final_residue p x (by omega)).2 ⟨hxpos,hxlt⟩⟩

theorem lucas_residues_mul_permutation__digit_final_residue (p a : Int) :
    prime p → (0<a ∧ a<p) →
    (((List.range' 1 (p-1).toNat).map Int.ofNat).map (fun x => Z.modulo (a*x) p)).Perm ((List.range' 1 (p-1).toNat).map Int.ofNat) := by
  intro hp ha
  have hp2 := prime_ge_2 p hp
  apply perm_of_nodup_subset_length _ _ _ (List.length_map _) _
  · apply nodup_map_on _ _ (NoDup_map_Zof_nat_seq__digit_final_residue _ _)
    intro x hx y hy he
    exact prime_mul_mod_cancel__digit_final_residue p a x y hp ha
      ((in_lucas_residues__digit_final_residue p x (by omega)).1 hx)
      ((in_lucas_residues__digit_final_residue p y (by omega)).1 hy) he
  · intro x hx
    rcases List.mem_map.mp hx with ⟨y,hy,he⟩
    subst x
    exact prime_mul_residue_in_lucas_residues__digit_final_residue p a y hp ha hy

theorem fold_right_Zmul_permutation__digit_final_residue (l1 l2 : List Int) :
    l1.Perm l2 → l1.foldr (· * ·) 1=l2.foldr (· * ·) 1 := by
  intro hp
  induction hp with
  | nil => rfl
  | cons a h ih => simp only [List.foldr_cons]; rw [ih]
  | swap a b l => simp only [List.foldr_cons]; grind
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem fold_right_Zmul_map_mod__digit_final_residue (p a : Int) (l : List Int) :
    p≠0 → Z.modulo ((l.map (fun x => Z.modulo (a*x) p)).foldr (· * ·) 1) p=
    Z.modulo (Z.pow a (Int.ofNat l.length)*l.foldr (· * ·) 1) p := by
  intro hp
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [List.map_cons,List.foldr_cons,List.length_cons,Z.pow,Z.modulo] at ih ⊢
    rw [Int.mul_fmod,Int.fmod_fmod,ih,←Int.mul_fmod]
    rw [Int.pow_succ]
    congr 1
    grind

theorem mod_eq_divide_sub__digit_final_residue (p x y : Int) :
    p≠0 → Z.modulo x p=Z.modulo y p → Z.divide p (x-y) := by
  intro _ h
  exact (Z.divide_iff_dvd _ _).2 (Int.dvd_of_fmod_eq_zero (Int.fmod_eq_fmod_iff_fmod_sub_eq_zero.mp h))

theorem divide_sub_mod_eq_one__digit_final_residue (p x : Int) :
    p≠0 → Z.divide p (x-1) → Z.modulo x p=Z.modulo 1 p := by
  intro _ h
  exact Int.fmod_eq_fmod_iff_fmod_sub_eq_zero.mpr (Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).1 h))

theorem lucas_residues_length__digit_final_residue (p : Int) : 1<p →
    Int.ofNat (((List.range' 1 (p-1).toNat).map Int.ofNat).length)=p-1 := by
  intro hp
  simp only [List.length_map,List.length_range',Int.ofNat_eq_coe]
  omega

theorem fermat_little_prime__digit_final_residue (p a : Int) :
    prime p → (0<a ∧ a<p) → Z.modulo (Z.pow a (p-1)) p=Z.modulo 1 p := by
  intro hp ha
  have hp2 := prime_ge_2 p hp
  let l := (List.range' 1 (p-1).toNat).map Int.ofNat
  let prod := l.foldr (· * ·) 1
  have he := fold_right_Zmul_permutation__digit_final_residue _ _ (lucas_residues_mul_permutation__digit_final_residue p a hp ha)
  have hm := fold_right_Zmul_map_mod__digit_final_residue p a l (by omega)
  rw [he] at hm
  have hd : p∣prod*(Z.pow a (Int.ofNat l.length)-1) := by
    have h := dvd_sub_of_mod_eq _ _ p hm.symm
    have heq : prod*(Z.pow a (Int.ofNat l.length)-1)=Z.pow a (Int.ofNat l.length)*prod-prod := by grind
    rw [heq]
    exact h
  have hn : ¬p∣prod := by
    intro h
    apply prime_product_not_divisible__digit_final_residue p l hp _ ((Z.divide_iff_dvd _ _).2 h)
    apply Forall.iff_forall_mem.mpr
    intro x hx
    exact (in_lucas_residues__digit_final_residue p x (by omega)).1 hx
  have hg : Int.gcd p prod=1 := by rw [Int.gcd_comm]; exact gcd1_prime p prod hp hn
  have hc := coprime_cancel_dvd p prod _ hg hd
  have ht := mod_eq_of_dvd_sub (Z.pow a (Int.ofNat l.length)) 1 p hc
  rw [lucas_residues_length__digit_final_residue p (by omega)] at ht
  exact ht

theorem digit_multiplicative_residue__digit_final_residue (upper lower p numerator denominator inverse : Int) :
    (0≤lower ∧ lower≤upper) → upper<p → PrimeForLucas p →
    DigitProductProgress upper lower p (lower+1) numerator denominator → ModularPower denominator (p-2) p inverse →
    Z.modulo (numerator*inverse) p=Z.modulo (LucasBinomialCoefficient upper lower) p := by
  intro hl hu hp hprog hinv
  have hp2 := hp.1
  have hprime := prime_for_lucas_prime__digit_final_residue p hp
  rcases hprog with ⟨hnum,hden⟩
  simp only [Int.add_sub_cancel] at hnum hden
  have hnz := digit_factorial_nonzero_mod_prime__digit_final_residue lower p ⟨hl.1,by omega⟩ hp
  have hdenrange : 0<denominator ∧ denominator<p := by
    rw [hden]
    have h0 := Int.fmod_nonneg_of_pos (DigitDenominatorPrefix lower) (by omega : 0<p)
    have hlt := Int.fmod_lt_of_pos (DigitDenominatorPrefix lower) (by omega : 0<p)
    unfold Z.modulo at *
    exact ⟨by omega,hlt⟩
  have hfermat := fermat_little_prime__digit_final_residue p denominator hprime hdenrange
  have hi : Z.modulo (denominator*inverse) p=1 := by
    unfold ModularPower at hinv
    rw [hinv]
    unfold Z.modulo
    rw [Int.mul_fmod,Int.fmod_fmod,←Int.mul_fmod]
    have hs : denominator*Z.pow denominator (p-2)=Z.pow denominator (p-1) := by
      have h := zpow_split denominator (p-1) (by omega)
      simpa only [show p-1-1=p-2 by omega] using h.symm
    unfold Z.modulo at hfermat
    rw [hs,hfermat]
    exact Int.fmod_eq_of_lt (by omega) (by omega)
  have hprod := lucas_binomial_range_product_z__digit_final_residue upper lower hl
  rw [hnum,←hprod]
  change (((LucasBinomialCoefficient upper lower*DigitDenominatorPrefix lower).fmod p)*inverse).fmod p=_
  rw [Int.mul_fmod,Int.fmod_fmod,←Int.mul_fmod]
  have he : ((DigitDenominatorPrefix lower)*inverse).fmod p=1 := by
    unfold Z.modulo at hden hi
    rw [Int.mul_fmod,←hden]
    have hdmod : denominator.fmod p=denominator := Int.fmod_eq_of_lt (by omega) hdenrange.2
    rw [←hdmod,←Int.mul_fmod]
    exact hi
  rw [Int.mul_assoc,Int.mul_fmod,he,Int.mul_one,Int.fmod_fmod]
  rfl

theorem lucas_nat_binomial_gt__lucas_digit_transition (n k : Nat) : n<k → LucasNatBinomial n k=0 :=
  lucas_nat_binomial_above__digit_final_residue n k

theorem lucas_nat_binomial_diag__lucas_digit_transition (n : Nat) : LucasNatBinomial n n=1 :=
  lucas_nat_binomial_diagonal__digit_final_residue n

theorem lucas_nat_binomial_factorial__lucas_digit_transition (n k : Nat) : k≤n →
    fact n=LucasNatBinomial n k*fact k*fact (n-k) := by
  intro hk
  exact (binomial_factorial n k hk).symm

theorem prime_for_lucas_standard__lucas_digit_transition (p : Int) : PrimeForLucas p → prime p :=
  prime_for_lucas_prime__digit_final_residue p

theorem prime_mod_mul_cancel__lucas_digit_transition (p a x y : Int) :
    prime p → rel_prime p a → Z.modulo (a*x) p=Z.modulo (a*y) p → Z.modulo x p=Z.modulo y p := by
  intro hp hr he
  have hg := Int.ofNat_inj.mp ((Zgcd_1_rel_prime p a).2 hr)
  have hd := dvd_sub_of_mod_eq _ _ _ he
  have hdm : p∣a*(x-y) := by
    have h : a*(x-y)=a*x-a*y := by grind
    rw [h]
    exact hd
  exact mod_eq_of_dvd_sub x y p (coprime_cancel_dvd p a (x-y) hg hdm)

private theorem factorial_coprime (p : Int) (r : Nat) (hp : prime p) (hr : (r:Int)<p) :
    Int.gcd p (Int.ofNat (fact r))=1 := by
  induction r with
  | zero => exact Int.gcd_one
  | succ r ih =>
    have hgr := ih (by omega)
    have hgp : Int.gcd p ((r+1:Int))=1 := by
      rw [Int.gcd_comm]
      apply gcd1_prime p _ hp
      intro hd
      have hle := Int.le_of_dvd (by omega : 0<(r+1:Int)) hd
      omega
    simp only [fact,Int.ofNat_eq_coe,Int.natCast_mul,Int.natCast_add,Int.natCast_one]
    rw [Int.gcd_mul_right_right_of_gcd_eq_one hgp]
    exact hgr

theorem prime_factorial_rel_prime__lucas_digit_transition (p r : Int) :
    prime p → (0≤r ∧ r<p) → rel_prime p (Int.ofNat (fact r.toNat)) := by
  intro hp hr
  apply (Zgcd_1_rel_prime _ _).1
  exact congrArg Int.ofNat (factorial_coprime p r.toNat hp (by omega))

theorem prime_factorial_nat_rel_prime__lucas_digit_transition (p r : Nat) :
    prime (Int.ofNat p) → r<p → rel_prime (Int.ofNat p) (Int.ofNat (fact r)) := by
  intro hp hr
  apply (Zgcd_1_rel_prime _ _).1
  exact congrArg Int.ofNat (factorial_coprime (Int.ofNat p) r hp (by simp only [Int.ofNat_eq_coe]; omega))

theorem nat_fold_mul_acc__lucas_digit_transition (l : List Nat) (c : Nat) :
    l.foldr (· * ·) c=l.foldr (· * ·) 1*c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons,ih]; grind

theorem factorial_as_range_product__lucas_digit_transition (n : Nat) :
    fact n=(List.range' 1 n).foldr (· * ·) 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_1_concat,nprod_append]
    simp only [List.foldr_cons,List.foldr_nil,Nat.mul_one,fact,ih]
    grind

theorem nat_range_product_app__lucas_digit_transition (start n m : Nat) :
    (List.range' start (n+m)).foldr (· * ·) 1=(List.range' start n).foldr (· * ·) 1*(List.range' (start+n) m).foldr (· * ·) 1 := by
  rw [←List.range'_append_1,nprod_append]

theorem nat_mod_mul_congr__lucas_digit_transition (p a a' b b' : Nat) :
    p≠0 → a%p=a'%p → b%p=b'%p → (a*b)%p=(a'*b')%p := by
  intro _ ha hb
  calc
    (a*b)%p=(a%p*(b%p))%p := Nat.mul_mod _ _ _
    _=(a'%p*(b'%p))%p := by rw [ha,hb]
    _=(a'*b')%p := (Nat.mul_mod _ _ _).symm

theorem z_mod_mul_congr__lucas_digit_transition (p a a' b b' : Int) :
    Z.modulo a p=Z.modulo a' p → Z.modulo b p=Z.modulo b' p → Z.modulo (a*b) p=Z.modulo (a'*b') p := by
  intro ha hb
  unfold Z.modulo at *
  calc
    (a*b).fmod p=(a.fmod p*b.fmod p).fmod p := Int.mul_fmod _ _ _
    _=(a'.fmod p*b'.fmod p).fmod p := by rw [ha,hb]
    _=(a'*b').fmod p := (Int.mul_fmod _ _ _).symm

theorem rel_prime_nat_power_cast__lucas_digit_transition (p : Int) (a n : Nat) :
    rel_prime p (Int.ofNat a) → rel_prime p (Int.ofNat (a^n)) := by
  intro hr
  have hg := Int.ofNat_inj.mp ((Zgcd_1_rel_prime p (Int.ofNat a)).2 hr)
  apply (Zgcd_1_rel_prime _ _).1
  have ht := Int.gcd_pow_right_of_gcd_eq_one (k:=n) hg
  have he : Int.ofNat (a^n)=(Int.ofNat a)^n := by simp only [Int.ofNat_eq_coe,Int.natCast_pow]
  rw [he]
  exact congrArg Int.ofNat ht

private def rangeProd (s c : Nat) : Nat := (List.range' s c).foldr (· * ·) 1
private def phi (p q r : Nat) : Nat := rangeProd (q*p+1) r
private def psi (p q : Nat) : Nat := ((List.range' 0 q).map (fun i => phi p i (p-1))).foldr (· * ·) 1

private theorem rangeProd_succ (s c : Nat) : rangeProd s (c+1)=rangeProd s c*(s+c) := by
  unfold rangeProd
  rw [List.range'_1_concat,nprod_append]
  simp

private theorem psi_succ (p q : Nat) : psi p (q+1)=psi p q*phi p q (p-1) := by
  unfold psi
  rw [List.range'_1_concat,List.map_append,nprod_append]
  simp

private theorem fact_mult (p q : Nat) (hp : 2≤p) : fact (q*p)=p^q*fact q*psi p q := by
  induction q with
  | zero => simp [psi,fact]
  | succ q ih =>
    have he : (q+1)*p=q*p+p := by grind
    rw [he,factorial_as_range_product__lucas_digit_transition,nat_range_product_app__lucas_digit_transition,
      ←factorial_as_range_product__lucas_digit_transition,ih]
    change p^q*fact q*psi p q*rangeProd (1+q*p) p=_
    have hb : rangeProd (1+q*p) p=phi p q (p-1)*((q+1)*p) := by
      have heq : p=(p-1)+1 := by omega
      have ht := rangeProd_succ (1+q*p) (p-1)
      rw [←heq] at ht
      rw [ht]
      have hs : 1+q*p=q*p+1 := by omega
      rw [hs]
      change phi p q (p-1)*(q*p+1+(p-1))=_
      congr 1
      omega
    rw [hb,psi_succ,Nat.pow_succ,fact]
    grind

private theorem fact_euclid (p q r : Nat) (hp : 2≤p) :
    fact (q*p+r)=p^q*fact q*phi p q r*psi p q := by
  rw [factorial_as_range_product__lucas_digit_transition,nat_range_product_app__lucas_digit_transition,
    ←factorial_as_range_product__lucas_digit_transition,fact_mult p q hp]
  have hs : 1+q*p=q*p+1 := by omega
  rw [hs]
  change p^q*fact q*psi p q*phi p q r=_
  grind

private theorem phi_mod (p q r : Nat) : phi p q r%p=fact r%p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    unfold phi at ih ⊢
    rw [rangeProd_succ,fact]
    have hs : q*p+1+r=(r+1)+q*p := by grind
    have hm : (q*p+1+r)%p=(r+1)%p := by rw [hs,Nat.add_mul_mod_self_right]
    calc
      _=(rangeProd (q*p+1) r%p*((q*p+1+r)%p))%p := Nat.mul_mod _ _ _
      _=(fact r%p*((r+1)%p))%p := by rw [ih,hm]
      _=(fact r*(r+1))%p := (Nat.mul_mod _ _ _).symm
      _=((r+1)*fact r)%p := by rw [Nat.mul_comm]

private theorem psi_mod (p q : Nat) (hp : 2≤p) : psi p q%p=(fact (p-1))^q%p := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [psi_succ,Nat.pow_succ]
    exact nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ (by omega) ih (phi_mod p q (p-1))

private theorem cast_mod (p n : Nat) : Z.modulo (Int.ofNat n) (Int.ofNat p)=Int.ofNat (n%p) :=
  (Int.ofNat_fmod n p).symm

private theorem nat_prime_cancel (p a x y : Nat) (hp : prime (Int.ofNat p))
    (hr : rel_prime (Int.ofNat p) (Int.ofNat a)) (he : (a*x)%p=(a*y)%p) : x%p=y%p := by
  have hez : Z.modulo (Int.ofNat a*Int.ofNat x) (Int.ofNat p)=Z.modulo (Int.ofNat a*Int.ofNat y) (Int.ofNat p) := by
    simpa only [Z.modulo,Int.ofNat_eq_coe,←Int.natCast_mul,←Int.ofNat_fmod] using congrArg Int.ofNat he
  have h := prime_mod_mul_cancel__lucas_digit_transition _ _ _ _ hp hr hez
  rw [cast_mod,cast_mod] at h
  exact Int.ofNat_inj.mp h

private theorem rel_prime_mul_nat (p : Int) (a b : Nat)
    (ha : rel_prime p (Int.ofNat a)) (hb : rel_prime p (Int.ofNat b)) : rel_prime p (Int.ofNat (a*b)) := by
  have hga := Int.ofNat_inj.mp ((Zgcd_1_rel_prime _ _).2 ha)
  have hgb := Int.ofNat_inj.mp ((Zgcd_1_rel_prime _ _).2 hb)
  simp only [Int.ofNat_eq_coe] at hga hgb
  apply (Zgcd_1_rel_prime _ _).1
  simp only [Z.gcd,Int.ofNat_eq_coe,Int.natCast_mul]
  rw [Int.gcd_mul_right_right_of_gcd_eq_one hga,hgb]
  rfl

private theorem factorial_factor_coprime (p a b e : Nat) (hp : prime (Int.ofNat p))
    (ha : a<p) (hb : b<p) (hp2 : 2≤p) :
    rel_prime (Int.ofNat p) (Int.ofNat (fact a*fact b*fact (p-1)^e)) := by
  apply rel_prime_mul_nat
  · exact rel_prime_mul_nat _ _ _
      (prime_factorial_nat_rel_prime__lucas_digit_transition p a hp ha)
      (prime_factorial_nat_rel_prime__lucas_digit_transition p b hp hb)
  · exact rel_prime_nat_power_cast__lucas_digit_transition _ _ _
      (prime_factorial_nat_rel_prime__lucas_digit_transition p (p-1) hp (by omega))

theorem lucas_nat_binomial_digit_step_core__lucas_digit_transition (p n k : Nat) :
    2≤p → prime (Int.ofNat p) → Z.modulo (Int.ofNat (LucasNatBinomial n k)) (Int.ofNat p)=
    Z.modulo (Int.ofNat (LucasNatBinomial (n/p) (k/p))*Int.ofNat (LucasNatBinomial (n%p) (k%p))) (Int.ofNat p) := by
  intro hp2 hp
  have hp0 : 0<p := by omega
  have hpn : p≠0 := by omega
  let N := n/p
  let K := k/p
  let n0 := n%p
  let k0 := k%p
  have hn : n=N*p+n0 := by simpa only [Nat.mul_comm] using (Nat.div_add_mod n p).symm
  have hk : k=K*p+k0 := by simpa only [Nat.mul_comm] using (Nat.div_add_mod k p).symm
  have hn0 : n0<p := Nat.mod_lt _ hp0
  have hk0 : k0<p := Nat.mod_lt _ hp0
  suffices h : LucasNatBinomial n k%p=(LucasNatBinomial N K*LucasNatBinomial n0 k0)%p by
    simpa only [Z.modulo,Int.ofNat_eq_coe,←Int.natCast_mul,←Int.ofNat_fmod] using congrArg Int.ofNat h
  by_cases hkn : k≤n
  · have hKN : K≤N := Nat.div_le_div_right hkn
    by_cases hd : k0≤n0
    · let D := N-K
      have hKD : K+D=N := by dsimp [D]; omega
      have hmul : K*p+D*p=N*p := by rw [←Nat.add_mul,hKD]
      have hdiff : n-k=D*p+(n0-k0) := by omega
      have hb := binomial_factorial n k hkn
      have hs := binomial_factorial N K hKN
      have hf1 : fact n=p^N*fact N*phi p N n0*psi p N := by rw [hn]; exact fact_euclid p N n0 hp2
      have hf2 : fact k=p^K*fact K*phi p K k0*psi p K := by rw [hk]; exact fact_euclid p K k0 hp2
      have hf3 : fact (n-k)=p^D*fact D*phi p D (n0-k0)*psi p D := by rw [hdiff]; exact fact_euclid p D (n0-k0) hp2
      have hpow : p^N=p^K*p^D := by rw [←hKD,Nat.pow_add]
      rw [hf1,hf2,hf3,hpow,←hs] at hb
      let A := phi p K k0*psi p K*phi p D (n0-k0)*psi p D
      have hb' : A*LucasNatBinomial n k=LucasNatBinomial N K*phi p N n0*psi p N := by
        apply Nat.eq_of_mul_eq_mul_left (n:=p^K*p^D*fact K*fact D)
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hp0) (Nat.pow_pos hp0)) (factorial_pos K)) (factorial_pos D))
        dsimp [A]
        grind
      let fp := fact (p-1)
      let F := fact k0*fact (n0-k0)*fp^N
      have hfp : fp^K*fp^D=fp^N := by rw [←Nat.pow_add,hKD]
      have hAF : A%p=F%p := by
        have ha : A%p=(fact k0*fp^K*fact (n0-k0)*fp^D)%p := by
          apply nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ hpn
          · apply nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ hpn
            · exact nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ hpn (phi_mod p K k0) (psi_mod p K hp2)
            · exact phi_mod p D (n0-k0)
          · exact psi_mod p D hp2
        rw [ha]
        congr 1
        dsimp [F]
        calc
          _=fact k0*fact (n0-k0)*(fp^K*fp^D) := by grind
          _=_ := by rw [hfp]
      have hBF : (phi p N n0*psi p N)%p=(LucasNatBinomial n0 k0*F)%p := by
        have he := nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ hpn (phi_mod p N n0) (psi_mod p N hp2)
        rw [he]
        congr 1
        have hbf := binomial_factorial n0 k0 hd
        dsimp [F,fp]
        rw [←hbf]
        grind
      have hc : (F*LucasNatBinomial n k)%p=(F*(LucasNatBinomial N K*LucasNatBinomial n0 k0))%p := by
        calc
          _=(A*LucasNatBinomial n k)%p := nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ hpn hAF.symm rfl
          _=(LucasNatBinomial N K*(phi p N n0*psi p N))%p := by rw [hb',Nat.mul_assoc]
          _=(LucasNatBinomial N K*(LucasNatBinomial n0 k0*F))%p := nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ hpn rfl hBF
          _=_ := by congr 1; grind
      exact nat_prime_cancel p F _ _ hp (factorial_factor_coprime p k0 (n0-k0) N hp hk0 (by omega) hp2) hc
    · have hdgt : n0<k0 := by omega
      have hKNlt : K<N := by
        by_cases he : K=N
        · rw [he] at hk
          omega
        · omega
      let D := N-(K+1)
      let r := p-(k0-n0)
      have hKD : K+D+1=N := by dsimp [D]; omega
      have hr : r<p := by dsimp [r]; omega
      have hmul : K*p+D*p+p=N*p := by
        calc
          _=(K+D+1)*p := by grind
          _=N*p := by rw [hKD]
      have hdiff : n-k=D*p+r := by dsimp [r]; omega
      have hb := binomial_factorial n k hkn
      have hs := binomial_factorial N K hKN
      have hf1 : fact n=p^N*fact N*phi p N n0*psi p N := by rw [hn]; exact fact_euclid p N n0 hp2
      have hf2 : fact k=p^K*fact K*phi p K k0*psi p K := by rw [hk]; exact fact_euclid p K k0 hp2
      have hf3 : fact (n-k)=p^D*fact D*phi p D r*psi p D := by rw [hdiff]; exact fact_euclid p D r hp2
      have hpow : p^N=p^K*p^D*p := by rw [←hKD,Nat.pow_succ,Nat.pow_add]
      have hfd : fact (N-K)=(N-K)*fact D := by
        have he : N-K=D+1 := by omega
        rw [he,fact]
      rw [hf1,hf2,hf3,hpow,←hs,hfd] at hb
      let A := phi p K k0*psi p K*phi p D r*psi p D
      have hb' : A*LucasNatBinomial n k=p*LucasNatBinomial N K*(N-K)*phi p N n0*psi p N := by
        apply Nat.eq_of_mul_eq_mul_left (n:=p^K*p^D*fact K*fact D)
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hp0) (Nat.pow_pos hp0)) (factorial_pos K)) (factorial_pos D))
        dsimp [A]
        grind
      let fp := fact (p-1)
      let F := fact k0*fact r*fp^(K+D)
      have hAF : A%p=F%p := by
        have ha : A%p=(fact k0*fp^K*fact r*fp^D)%p := by
          apply nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ hpn
          · apply nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ hpn
            · exact nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ hpn (phi_mod p K k0) (psi_mod p K hp2)
            · exact phi_mod p D r
          · exact psi_mod p D hp2
        rw [ha]
        congr 1
        dsimp [F]
        rw [Nat.pow_add]
        grind
      have hc : (F*LucasNatBinomial n k)%p=(F*0)%p := by
        calc
          _=(A*LucasNatBinomial n k)%p := nat_mod_mul_congr__lucas_digit_transition p _ _ _ _ hpn hAF.symm rfl
          _=0 := by rw [hb']; simp only [Nat.mul_assoc,Nat.mul_mod_right]
          _=(F*0)%p := by simp
      have hz := nat_prime_cancel p F _ 0 hp (factorial_factor_coprime p k0 r (K+D) hp hk0 hr hp2) hc
      rw [lucas_nat_binomial_above__digit_final_residue n0 k0 hdgt]
      simpa using hz
  · have hnk : n<k := by omega
    rw [lucas_nat_binomial_above__digit_final_residue n k hnk]
    by_cases hKN : K≤N
    · have hNK : N≤K := Nat.div_le_div_right (Nat.le_of_lt hnk)
      have he : K=N := by omega
      rw [he] at hk
      have hd : n0<k0 := by omega
      rw [lucas_nat_binomial_above__digit_final_residue n0 k0 hd]
      simp
    · rw [lucas_nat_binomial_above__digit_final_residue N K (by omega)]
      simp

theorem lucas_nat_binomial_digit_step__lucas_digit_transition (upper lower p : Int) :
    0≤upper → 0≤lower → PrimeForLucas p →
    Z.modulo (LucasBinomialCoefficient upper lower) p=
    Z.modulo (LucasBinomialCoefficient (Z.div upper p) (Z.div lower p)*LucasBinomialCoefficient (Z.modulo upper p) (Z.modulo lower p)) p := by
  intro hu hl hp
  have hp2 := hp.1
  have hc : Int.ofNat p.toNat=p := by simp only [Int.ofNat_eq_coe]; omega
  have hu' : Int.ofNat upper.toNat=upper := by simp only [Int.ofNat_eq_coe]; omega
  have hl' : Int.ofNat lower.toNat=lower := by simp only [Int.ofNat_eq_coe]; omega
  have hcore := lucas_nat_binomial_digit_step_core__lucas_digit_transition p.toNat upper.toNat lower.toNat
    (by omega) (by rw [hc]; exact prime_for_lucas_prime__digit_final_residue p hp)
  have hdiv (x : Int) (hx : 0≤x) : (Z.div x p).toNat=x.toNat/p.toNat := by
    have he : Int.ofNat x.toNat=x := by simp only [Int.ofNat_eq_coe]; omega
    conv => lhs; rw [←he,←hc]
    unfold Z.div
    simp only [Int.ofNat_eq_coe,←Int.ofNat_fdiv,Int.toNat_natCast]
  have hmod (x : Int) (hx : 0≤x) : (Z.modulo x p).toNat=x.toNat%p.toNat := by
    have he : Int.ofNat x.toNat=x := by simp only [Int.ofNat_eq_coe]; omega
    conv => lhs; rw [←he,←hc]
    rw [cast_mod]
    rfl
  unfold LucasBinomialCoefficient
  rw [hdiv upper hu,hdiv lower hl,hmod upper hu,hmod lower hl]
  rw [hc] at hcore
  exact hcore

theorem lucas_prefix_product_succ__lucas_digit_transition (upper lower p : Int) (processed : Nat) :
    p≠0 → LucasPrefixProduct upper lower p (processed+1)=
    Z.modulo (LucasPrefixProduct upper lower p processed*Z.modulo (LucasBinomialCoefficient (LucasDigit upper p processed) (LucasDigit lower p processed)) p) p := by
  intro hp
  unfold LucasPrefixProduct
  rw [List.range'_1_concat,List.map_append,zprod_append]
  simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,Int.mul_one,Nat.zero_add]
  unfold Z.modulo
  rw [Int.mul_fmod,Int.mul_fmod]
  simp only [Int.fmod_fmod]

theorem lucas_progress_advance__lucas_digit_transition (original_upper original_lower p upper lower result retval : Int) :
    0≤original_upper → 0≤original_lower → 0≤upper → 0≤lower → 0≤result → 0≤retval →
    PrimeForLucas p → BinomialDigitResidue (Z.rem upper p) (Z.rem lower p) p retval →
    LucasProgress original_upper original_lower p upper lower result →
    LucasProgress original_upper original_lower p (Z.quot upper p) (Z.quot lower p) (Z.rem (result*retval) p) := by
  intro hou hol hu hl hr hv hp hdi hprog
  have hp2 := hp.1
  rcases hprog with ⟨processed,hup,hlp,hrp,hres⟩
  have hpow := zpow_pos p (Int.ofNat processed) (by omega) (by simp only [Int.ofNat_eq_coe]; omega)
  have hpowS : Z.pow p (Int.ofNat (processed+1))=Z.pow p (Int.ofNat processed)*p := Int.pow_succ p processed
  have hremu : Z.rem upper p=Z.modulo upper p := (Int.fmod_eq_tmod_of_nonneg hu (by omega)).symm
  have hreml : Z.rem lower p=Z.modulo lower p := (Int.fmod_eq_tmod_of_nonneg hl (by omega)).symm
  have hremr : Z.rem (result*retval) p=Z.modulo (result*retval) p :=
    (Int.fmod_eq_tmod_of_nonneg (Int.mul_nonneg hr hv) (by omega)).symm
  have hquotu : Z.quot upper p=Z.div upper p := (Int.fdiv_eq_tdiv_of_nonneg hu (by omega)).symm
  have hquotl : Z.quot lower p=Z.div lower p := (Int.fdiv_eq_tdiv_of_nonneg hl (by omega)).symm
  have hdiv (x : Int) : Z.div (Z.div x (Z.pow p (Int.ofNat processed))) p=
      Z.div x (Z.pow p (Int.ofNat (processed+1))) := by
    rw [hpowS]
    unfold Z.div
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega),Int.fdiv_eq_ediv_of_nonneg _ (by omega),
      Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt (Int.mul_pos hpow (by omega)))]
    exact Int.ediv_ediv (by omega)
  refine ⟨processed+1,?_,?_,?_,?_⟩
  · rw [hquotu,hup]
    exact hdiv original_upper
  · rw [hquotl,hlp]
    exact hdiv original_lower
  · rw [hremr,lucas_prefix_product_succ__lucas_digit_transition _ _ _ _ (by omega),←hrp]
    unfold LucasDigit
    rw [←hup,←hlp]
    unfold BinomialDigitResidue at hdi
    rw [hremu,hreml] at hdi
    rw [hdi]
  · rw [hremr,hquotu,hquotl,hres]
    have hstep := lucas_nat_binomial_digit_step__lucas_digit_transition upper lower p hu hl hp
    unfold BinomialDigitResidue at hdi
    rw [hremu,hreml] at hdi
    let Q := LucasBinomialCoefficient (Z.div upper p) (Z.div lower p)
    let D := LucasBinomialCoefficient (Z.modulo upper p) (Z.modulo lower p)
    have hd : Z.modulo D p=Z.modulo retval p := by
      rw [hdi]
      exact (Int.fmod_fmod _ _).symm
    calc
      _=Z.modulo (result*(Q*D)) p := z_mod_mul_congr__lucas_digit_transition p _ _ _ _ rfl hstep
      _=Z.modulo ((result*D)*Q) p := by congr 1; grind
      _=Z.modulo ((result*retval)*Q) p := z_mod_mul_congr__lucas_digit_transition p _ _ _ _
        (z_mod_mul_congr__lucas_digit_transition p _ _ _ _ rfl hd) rfl
      _=_ := by
        change ((result*retval)*Q).fmod p=(((result*retval).fmod p)*Q).fmod p
        symm
        rw [Int.mul_fmod,Int.fmod_fmod,←Int.mul_fmod]

theorem lucas_binomial_zero_from_low_digit__lucas_digit_transition (upper lower p : Int) :
    0≤upper → 0≤lower → PrimeForLucas p → Z.rem upper p<Z.rem lower p →
    Z.modulo (LucasBinomialCoefficient upper lower) p=0 := by
  intro hu hl hp hd
  have hp2 := hp.1
  have hremu : Z.rem upper p=Z.modulo upper p := (Int.fmod_eq_tmod_of_nonneg hu (by omega)).symm
  have hreml : Z.rem lower p=Z.modulo lower p := (Int.fmod_eq_tmod_of_nonneg hl (by omega)).symm
  rw [hremu,hreml] at hd
  have hu0 := Int.fmod_nonneg_of_pos upper (by omega : 0<p)
  have hl0 := Int.fmod_nonneg_of_pos lower (by omega : 0<p)
  have hlt : (Z.modulo upper p).toNat<(Z.modulo lower p).toNat := by unfold Z.modulo at *; omega
  have hs := lucas_nat_binomial_digit_step__lucas_digit_transition upper lower p hu hl hp
  unfold LucasBinomialCoefficient at hs
  rw [lucas_nat_binomial_above__digit_final_residue _ _ hlt] at hs
  simpa only [LucasBinomialCoefficient,Int.ofNat_eq_coe,Int.natCast_zero,Int.mul_zero,Z.modulo,Int.zero_fmod] using hs

theorem lucas_progress_terminal_residue__lucas_terminal_return (original_upper original_lower p result : Int) :
    0<p → (0≤result ∧ result<p) → LucasProgress original_upper original_lower p 0 0 result →
    result=Z.modulo (LucasBinomialCoefficient original_upper original_lower) p := by
  rintro hp hr ⟨processed,hu,hl,hs,hc⟩
  have h00 : LucasBinomialCoefficient 0 0=1 := rfl
  rw [h00,Int.mul_one] at hc
  rw [show Z.modulo result p=result from Int.fmod_eq_of_lt hr.1 hr.2] at hc
  exact hc.symm
end SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_lib
namespace SimpleC.EE.LLM_bench.Algorithms.lucas_theorem
export lucas_theorem_lib (ModularPower PrimeForLucas LucasNatBinomial LucasBinomialCoefficient BinomialDigitResidue LucasBinomialResidue DigitEffectiveLower LucasRangeProduct DigitNumeratorPrefix DigitDenominatorPrefix DigitBinomialMachineSafe LucasDigit LucasPrefixProduct LucasMachineSafe DigitProductProgress LucasProgress)
end SimpleC.EE.LLM_bench.Algorithms.lucas_theorem
