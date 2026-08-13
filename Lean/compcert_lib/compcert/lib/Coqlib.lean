import Std.Tactic
import Init.Data.Int.Bitwise.Basic
import Init.Data.Int.Gcd
import Init.Data.Nat.Bitwise.Lemmas

/-!
The arithmetic part of CompCert uses Coq's `Z`. The project maps its carrier to
Lean `Int`, while this namespace preserves the operations whose edge behavior
is not identical to Lean's default typeclass notation.
-/

namespace Z

def abs (x : Int) : Int :=
  Int.ofNat x.natAbs

def gcd (x y : Int) : Int :=
  Int.ofNat (Int.gcd x y)

def pow (base exponent : Int) : Int :=
  match exponent with
  | .ofNat n => base ^ n
  | .negSucc _ => 0

def div (x y : Int) : Int :=
  Int.fdiv x y

def modulo (x y : Int) : Int :=
  Int.fmod x y

def rem (x y : Int) : Int :=
  Int.tmod x y

def quot (x y : Int) : Int :=
  Int.tdiv x y

def divide (divisor dividend : Int) : Prop :=
  exists quotient, dividend = quotient * divisor

theorem mod_recombine (x a b : Int) (ha : a > 0) (hb : b > 0) :
    modulo x (a * b) = modulo (div x b) a * b + modulo x b := by
  let q := div x b
  let r := modulo x b
  let q' := div q a
  let r' := modulo q a
  have hab : 0 < a * b := Int.mul_pos ha hb
  have hx : q * b + r = x := by
    exact Int.fdiv_mul_add_fmod x b
  have hq : q' * a + r' = q := by
    exact Int.fdiv_mul_add_fmod q a
  have hr : 0 <= r ∧ r < b := by
    exact ⟨Int.fmod_nonneg_of_pos x hb, Int.fmod_lt_of_pos x hb⟩
  have hr' : 0 <= r' ∧ r' < a := by
    exact ⟨Int.fmod_nonneg_of_pos q ha, Int.fmod_lt_of_pos q ha⟩
  have hrem : 0 <= r' * b + r ∧ r' * b + r < a * b := by
    constructor
    · exact Int.add_nonneg (Int.mul_nonneg hr'.1 (Int.le_of_lt hb)) hr.1
    · have hs : r' + 1 <= a := by omega
      have hmul : (r' + 1) * b <= a * b :=
        Int.mul_le_mul_of_nonneg_right hs (Int.le_of_lt hb)
      calc
        r' * b + r < r' * b + b := Int.add_lt_add_left hr.2 _
        _ = (r' + 1) * b := by rw [Int.add_mul, Int.one_mul]
        _ <= a * b := hmul
  unfold modulo div
  have huniq := (Int.fdiv_fmod_unique
    (a := x) (b := a * b) (r := r' * b + r) (q := q') hab).mpr
  have hresult := huniq (by
    constructor
    · dsimp only [q, r, q', r'] at hx hq ⊢
      calc
        r' * b + r + a * b * q' = (q' * a + r') * b + r := by
          rw [Int.add_mul]
          ac_rfl
        _ = q * b + r := by rw [hq]
        _ = x := hx
    · exact hrem)
  exact hresult.2

def shiftl (x : Int) : Int -> Int
  | .ofNat n => x <<< n
  | .negSucc n => x >>> (n + 1)

def shiftr (x n : Int) : Int :=
  shiftl x (-n)

def land : Int -> Int -> Int
  | .ofNat x, .ofNat y => .ofNat (Nat.land x y)
  | .ofNat x, .negSucc y => .ofNat (Nat.xor x (Nat.land x y))
  | .negSucc x, .ofNat y => .ofNat (Nat.xor y (Nat.land x y))
  | .negSucc x, .negSucc y => .negSucc (Nat.lor x y)

def lor : Int -> Int -> Int
  | .ofNat x, .ofNat y => .ofNat (Nat.lor x y)
  | .ofNat x, .negSucc y => .negSucc (Nat.xor y (Nat.land x y))
  | .negSucc x, .ofNat y => .negSucc (Nat.xor x (Nat.land x y))
  | .negSucc x, .negSucc y => .negSucc (Nat.land x y)

def lxor : Int -> Int -> Int
  | .ofNat x, .ofNat y => .ofNat (Nat.xor x y)
  | .ofNat x, .negSucc y => .negSucc (Nat.xor x y)
  | .negSucc x, .ofNat y => .negSucc (Nat.xor x y)
  | .negSucc x, .negSucc y => .ofNat (Nat.xor x y)

def lnot : Int -> Int
  | .ofNat n => .negSucc n
  | .negSucc n => .ofNat n

@[simp] theorem lnot_ofNat (n : Nat) : lnot (Int.ofNat n) = Int.negSucc n := rfl

@[simp] theorem lnot_negSucc (n : Nat) : lnot (Int.negSucc n) = Int.ofNat n := rfl

def ldiff (x y : Int) : Int :=
  land x (lnot y)

def testbit (x index : Int) : Bool :=
  match index with
  | .ofNat n =>
      match x with
      | .ofNat value => Nat.testBit value n
      | .negSucc value => !(Nat.testBit value n)
  | .negSucc _ => false

def ones (width : Int) : Int :=
  pow 2 width - 1

private theorem eq_of_testbit_eq {x y : Int}
    (h : forall i : Nat, testbit x (Int.ofNat i) = testbit y (Int.ofNat i)) :
    x = y := by
  cases x with
  | ofNat x =>
      cases y with
      | ofNat y =>
          congr 1
          apply Nat.eq_of_testBit_eq
          intro i
          exact h i
      | negSucc y =>
          have hx : Nat.testBit x (x + y + 1) = false := by
            apply Nat.testBit_lt_two_pow
            exact Nat.lt_trans (by omega) Nat.lt_two_pow_self
          have hy : Nat.testBit y (x + y + 1) = false := by
            apply Nat.testBit_lt_two_pow
            exact Nat.lt_trans (by omega) Nat.lt_two_pow_self
          have hxy := h (x + y + 1)
          simp [testbit, hx, hy] at hxy
  | negSucc x =>
      cases y with
      | ofNat y =>
          have hx : Nat.testBit x (x + y + 1) = false := by
            apply Nat.testBit_lt_two_pow
            exact Nat.lt_trans (by omega) Nat.lt_two_pow_self
          have hy : Nat.testBit y (x + y + 1) = false := by
            apply Nat.testBit_lt_two_pow
            exact Nat.lt_trans (by omega) Nat.lt_two_pow_self
          have hxy := h (x + y + 1)
          simp [testbit, hx, hy] at hxy
      | negSucc y =>
          congr 1
          apply Nat.eq_of_testBit_eq
          intro i
          have hxy := h i
          simpa [testbit] using congrArg (fun b => !b) hxy

theorem bits_inj' (a b : Int)
    (h : forall n : Int, 0 <= n -> testbit a n = testbit b n) :
    a = b := by
  apply eq_of_testbit_eq
  intro i
  exact h (Int.ofNat i) (Int.ofNat_zero_le i)

private theorem nat_testBit_land (x y i : Nat) :
    Nat.testBit (Nat.land x y) i = (Nat.testBit x i && Nat.testBit y i) := by
  simpa [HAnd.hAnd, AndOp.and] using Nat.testBit_and x y i

private theorem nat_testBit_lor (x y i : Nat) :
    Nat.testBit (Nat.lor x y) i = (Nat.testBit x i || Nat.testBit y i) := by
  simpa [HOr.hOr, OrOp.or] using Nat.testBit_or x y i

private theorem nat_testBit_xor (x y i : Nat) :
    Nat.testBit (Nat.xor x y) i = Bool.xor (Nat.testBit x i) (Nat.testBit y i) := by
  simpa [HXor.hXor, XorOp.xor] using Nat.testBit_xor x y i

private theorem bool_xor_and_left (a b : Bool) :
    Bool.xor a (a && b) = (a && !b) := by
  cases a <;> cases b <;> decide

private theorem bool_xor_and_right (a b : Bool) :
    Bool.xor b (a && b) = (!a && b) := by
  cases a <;> cases b <;> decide

@[simp] theorem land_spec (a b n : Int) :
    testbit (land a b) n = (testbit a n && testbit b n) := by
  cases a <;> cases b <;> cases n <;>
    simp [land, testbit, nat_testBit_land, nat_testBit_lor, nat_testBit_xor,
      bool_xor_and_left, bool_xor_and_right, Bool.xor]

theorem land_zero (a : Int) : land a 0 = 0 := by
  apply eq_of_testbit_eq
  intro i
  rw [land_spec]
  have hz : testbit (0 : Int) (Int.ofNat i) = false := by simp [testbit]
  rw [hz]
  simp

theorem zero_land (a : Int) : land 0 a = 0 := by
  apply eq_of_testbit_eq
  intro i
  rw [land_spec]
  have hz : testbit (0 : Int) (Int.ofNat i) = false := by simp [testbit]
  rw [hz]
  simp

@[simp] theorem lor_spec (a b n : Int) :
    testbit (lor a b) n = (testbit a n || testbit b n) := by
  cases a <;> cases b <;> cases n <;>
    simp [lor, testbit, nat_testBit_land, nat_testBit_lor, nat_testBit_xor,
      bool_xor_and_left, bool_xor_and_right, Bool.xor]

@[simp] theorem lxor_spec (a b n : Int) :
    testbit (lxor a b) n = Bool.xor (testbit a n) (testbit b n) := by
  cases a <;> cases b <;> cases n <;>
    simp [lxor, testbit, nat_testBit_xor, Bool.xor]

@[simp] theorem ldiff_spec (a b n : Int) :
    testbit (ldiff a b) n = (testbit a n && !(testbit b n)) := by
  cases a <;> cases b <;> cases n <;>
    simp [ldiff, land, lnot, testbit, nat_testBit_land, nat_testBit_lor,
      nat_testBit_xor, bool_xor_and_left, bool_xor_and_right, Bool.xor]

theorem land_assoc (a b c : Int) : land a (land b c) = land (land a b) c := by
  apply eq_of_testbit_eq
  intro i
  simp [Bool.and_assoc]

theorem land_comm (a b : Int) : land a b = land b a := by
  apply eq_of_testbit_eq
  intro i
  simp [Bool.and_comm]

theorem land_diag (a : Int) : land a a = a := by
  apply eq_of_testbit_eq
  intro i
  simp

private theorem int_two_pow (n : Nat) :
    (2 : Int) ^ n = Int.ofNat (2 ^ n) := by
  exact (Int.natCast_pow 2 n).symm

private theorem modulo_pow_ofNat (x n : Nat) :
    modulo (Int.ofNat x) (pow 2 (Int.ofNat n)) = Int.ofNat (x % 2 ^ n) := by
  simp only [modulo, pow]
  rw [int_two_pow]
  change (Int.ofNat x).fmod (Int.ofNat (2 ^ n)) = Int.ofNat (x % 2 ^ n)
  exact (Int.ofNat_fmod x (2 ^ n)).symm

private theorem modulo_pow_negSucc (x n : Nat) :
    modulo (Int.negSucc x) (pow 2 (Int.ofNat n)) =
      Int.ofNat (2 ^ n - (x % 2 ^ n + 1)) := by
  simp only [modulo, pow]
  rw [int_two_pow]
  change (Int.negSucc x).fmod (Int.ofNat (2 ^ n)) = _
  simp only [Int.ofNat_eq_coe]
  rw [Int.fmod_eq_emod_of_nonneg]
  · rw [Int.negSucc_emod x (Int.natCast_pos.mpr (Nat.two_pow_pos n))]
    rw [Int.ofNat_mod_ofNat]
    have hmod : x % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
    rw [Int.ofNat_sub (show x % 2 ^ n + 1 <= 2 ^ n by omega)]
    omega
  · exact Int.ofNat_zero_le (2 ^ n)

theorem mod_pow2_bits_low (a n m : Int) (h : m < n) :
    testbit (modulo a (pow 2 n)) m = testbit a m := by
  cases n with
  | negSucc n =>
      simp [pow, modulo]
  | ofNat n =>
      cases m with
      | negSucc m => simp [testbit]
      | ofNat m =>
          cases a with
          | ofNat a =>
              rw [modulo_pow_ofNat]
              change Nat.testBit (a % 2 ^ n) m = Nat.testBit a m
              rw [Nat.testBit_mod_two_pow]
              have hmn : m < n := Int.ofNat_lt.mp h
              simp [hmn]
          | negSucc a =>
              rw [modulo_pow_negSucc]
              have hmod : a % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
              change Nat.testBit (2 ^ n - (a % 2 ^ n + 1)) m = !Nat.testBit a m
              rw [Nat.testBit_two_pow_sub_succ hmod]
              have hmn : m < n := Int.ofNat_lt.mp h
              simp [hmn, Nat.testBit_mod_two_pow]

theorem mod_pow2_bits_high (a n m : Int) (h : 0 <= n ∧ n <= m) :
    testbit (modulo a (pow 2 n)) m = false := by
  cases n with
  | negSucc n => omega
  | ofNat n =>
      cases m with
      | negSucc m => omega
      | ofNat m =>
          have hnm : n <= m := Int.ofNat_le.mp h.2
          cases a with
          | ofNat a =>
              rw [modulo_pow_ofNat]
              apply Nat.testBit_lt_two_pow
              exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos n))
                (Nat.pow_le_pow_right (by decide) hnm)
          | negSucc a =>
              rw [modulo_pow_negSucc]
              apply Nat.testBit_lt_two_pow
              have hmod : a % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
              have hbound : 2 ^ n - (a % 2 ^ n + 1) < 2 ^ n := by omega
              exact Nat.lt_of_lt_of_le hbound
                (Nat.pow_le_pow_right (by decide) hnm)

private theorem ones_ofNat (n : Nat) :
    ones (Int.ofNat n) = Int.ofNat (2 ^ n - 1) := by
  simp only [ones, pow]
  rw [int_two_pow]
  change Int.ofNat (2 ^ n) - 1 = Int.ofNat (2 ^ n - 1)
  exact (Int.ofNat_sub (Nat.two_pow_pos n)).symm

private theorem testbit_ones (n : Int) (i : Nat) (hn : 0 <= n) :
    testbit (ones n) (Int.ofNat i) = decide ((Int.ofNat i) < n) := by
  cases n with
  | negSucc n => omega
  | ofNat n =>
      rw [ones_ofNat]
      change Nat.testBit (2 ^ n - 1) i = decide (Int.ofNat i < Int.ofNat n)
      rw [Nat.testBit_two_pow_sub_one]
      congr 1
      exact propext Int.ofNat_lt.symm

theorem land_ones (a n : Int) (hn : 0 <= n) :
    land a (ones n) = modulo a (pow 2 n) := by
  apply eq_of_testbit_eq
  intro i
  by_cases hi : (Int.ofNat i) < n
  · rw [land_spec, testbit_ones n i hn, mod_pow2_bits_low a n (Int.ofNat i) hi]
    simp only [hi, decide_true, Bool.and_true]
  · rw [land_spec, testbit_ones n i hn,
      mod_pow2_bits_high a n (Int.ofNat i) (by omega)]
    simp only [hi, decide_false, Bool.and_false]

theorem ones_mod_pow2 (n m : Int) (h : 0 <= m ∧ m <= n) :
    modulo (ones n) (pow 2 m) = ones m := by
  rw [← land_ones (ones n) m h.1]
  apply eq_of_testbit_eq
  intro i
  rw [land_spec, testbit_ones n i (by omega), testbit_ones m i h.1]
  by_cases hi : (Int.ofNat i) < m
  · have hin : (Int.ofNat i) < n := by omega
    simp only [hi, hin, decide_true, Bool.and_true]
  · simp only [hi, decide_false, Bool.and_false]

end Z

theorem Zmod_recombine (x a b : Int) (ha : a > 0) (hb : b > 0) :
    Z.modulo x (a * b) = Z.modulo (Z.div x b) a * b + Z.modulo x b :=
  Z.mod_recombine x a b ha hb

namespace CoqZ

scoped instance : HPow Int Int Int where
  hPow := Z.pow

end CoqZ
