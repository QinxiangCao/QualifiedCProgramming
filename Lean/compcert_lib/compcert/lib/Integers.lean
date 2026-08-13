import compcert.lib.ZArithCompat
import Lean.Elab.Tactic.Grind

def two_power_nat (n : Nat) : Int :=
  (2 : Int) ^ n

def two_p (n : Int) : Int :=
  Z.pow 2 n

theorem two_p_equiv (n : Int) :
    two_p n = Z.pow 2 n := rfl

theorem two_power_nat_equiv (n : Nat) :
    two_power_nat n = Z.pow 2 (Int.ofNat n) := by
  simp only [two_power_nat, Z.pow]

inductive comparison where
  | Ceq
  | Cne
  | Clt
  | Cle
  | Cgt
  | Cge
  deriving DecidableEq, Repr

export comparison (Ceq Cne Clt Cle Cgt Cge)

namespace Zbits

def eqmod (modul x y : Int) : Prop :=
  exists k : Int, x = k * modul + y

theorem eqmod_refl (modul x : Int) : eqmod modul x x := by
  exact ⟨0, by simp⟩

theorem eqmod_refl2 (modul x y : Int) (h : x = y) : eqmod modul x y := by
  subst y
  exact eqmod_refl modul x

theorem eqmod_sym (modul x y : Int) (h : eqmod modul x y) :
    eqmod modul y x := by
  rcases h with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  rw [hk]
  rw [Int.neg_mul]
  exact (Int.neg_add_cancel_left (k * modul) y).symm

theorem eqmod_trans (modul x y z : Int)
    (hxy : eqmod modul x y) (hyz : eqmod modul y z) :
    eqmod modul x z := by
  rcases hxy with ⟨k, hk⟩
  rcases hyz with ⟨l, hl⟩
  refine ⟨k + l, ?_⟩
  rw [hk, hl]
  simp [Int.add_mul, Int.add_assoc]

theorem eqmod_mod (modul x : Int) :
    eqmod modul x (Z.modulo x modul) := by
  refine ⟨Z.div x modul, ?_⟩
  exact (Int.fdiv_mul_add_fmod x modul).symm

theorem eqmod_mod_eq (modul : Int) (_hmod : modul > 0) (x y : Int)
    (h : eqmod modul x y) :
    Z.modulo x modul = Z.modulo y modul := by
  rcases h with ⟨k, hk⟩
  rw [hk, Int.add_comm]
  exact Int.add_mul_fmod_self_right y k modul

theorem Ztestbit_above (n : Nat) (x i : Int)
    (hx : 0 <= x ∧ x < two_power_nat n) (hi : i >= Int.ofNat n) :
    Z.testbit x i = false := by
  cases x with
  | negSucc x => omega
  | ofNat x =>
      cases i with
      | negSucc i =>
          have hbad : 0 <= Int.negSucc i :=
            Int.le_trans (Int.ofNat_zero_le n) hi
          simp at hbad
      | ofNat i =>
          change Nat.testBit x i = false
          apply Nat.testBit_lt_two_pow
          have hp : (2 : Int) ^ n = Int.ofNat (2 ^ n) :=
            (Int.natCast_pow 2 n).symm
          rw [two_power_nat, hp] at hx
          have hxn : x < 2 ^ n := Int.ofNat_lt.mp hx.2
          have hni : n <= i := Int.ofNat_le.mp hi
          exact Nat.lt_of_lt_of_le hxn (Nat.pow_le_pow_right (by decide) hni)

private theorem neg_two_p_ofNat (n : Nat) :
    -(two_p (Int.ofNat n)) = Int.negSucc (2 ^ n - 1) := by
  have hp : two_p (Int.ofNat n) = Int.ofNat (2 ^ n) := by
    simp only [two_p, Z.pow]
    exact (Int.natCast_pow 2 n).symm
  rw [hp]
  have hsucc : 2 ^ n = (2 ^ n - 1) + 1 := by
    have := Nat.two_pow_pos n
    omega
  rw [hsucc]
  exact Int.neg_ofNat_succ (2 ^ n - 1)

theorem Ztestbit_neg_two_p (n i : Int) (hn : 0 <= n) (hi : 0 <= i) :
    Z.testbit (-(two_p n)) i = if i < n then false else true := by
  cases n with
  | negSucc n => omega
  | ofNat n =>
      cases i with
      | negSucc i => omega
      | ofNat i =>
          rw [neg_two_p_ofNat]
          change Bool.not (Nat.testBit (2 ^ n - 1) i) =
            if Int.ofNat i < Int.ofNat n then false else true
          rw [Nat.testBit_two_pow_sub_one]
          by_cases hlt : i < n
          · simp [hlt]
          · simp [hlt]

private theorem modulo_two_eq_bit (x : Int) :
    Z.modulo x 2 = if Z.testbit x 0 then 1 else 0 := by
  have hr0 : 0 <= Z.modulo x 2 := by
    exact Int.fmod_nonneg_of_pos x (by decide)
  have hr2 : Z.modulo x 2 < 2 := by
    exact Int.fmod_lt_of_pos x (by decide)
  have hr : Z.modulo x 2 = 0 ∨ Z.modulo x 2 = 1 := by omega
  have hbit := Z.mod_pow2_bits_low x 1 0 (by decide)
  have hp : Z.pow 2 1 = 2 := by decide
  rw [hp] at hbit
  rcases hr with hr | hr <;> rw [hr] at hbit ⊢ <;>
    simp [Z.testbit] at hbit ⊢ <;> assumption

private theorem div_mod_add_of_testbit_zero_disjoint (x y : Int)
    (hxy : (Z.testbit x 0 && Z.testbit y 0) = false) :
    Z.div (x + y) 2 = Z.div x 2 + Z.div y 2 ∧
      Z.modulo (x + y) 2 = Z.modulo x 2 + Z.modulo y 2 := by
  have hrx := modulo_two_eq_bit x
  have hry := modulo_two_eq_bit y
  have hrange :
      0 <= Z.modulo x 2 + Z.modulo y 2 ∧
        Z.modulo x 2 + Z.modulo y 2 < 2 := by
    rw [hrx, hry]
    cases hx : Z.testbit x 0 <;> cases hy : Z.testbit y 0 <;>
      simp [hx, hy] at hxy ⊢
  have hxdiv := Int.fdiv_mul_add_fmod x 2
  have hydiv := Int.fdiv_mul_add_fmod y 2
  have huniq := (Int.fdiv_fmod_unique
    (a := x + y) (b := 2)
    (r := Z.modulo x 2 + Z.modulo y 2)
    (q := Z.div x 2 + Z.div y 2) (by decide)).mpr
  have hresult := huniq (by
    constructor
    · dsimp only [Z.div, Z.modulo] at hxdiv hydiv ⊢
      omega
    · exact hrange)
  exact hresult

private theorem testbit_succ_div_two (x : Int) (i : Nat) :
    Z.testbit x (Int.ofNat (i + 1)) =
      Z.testbit (Z.div x 2) (Int.ofNat i) := by
  have hdiv : Z.div x 2 = x >>> 1 := by
    unfold Z.div
    rw [Int.fdiv_eq_ediv_of_nonneg x (by decide)]
    simpa using (Int.shiftRight_eq_div_pow x 1).symm
  rw [hdiv]
  cases x with
  | ofNat x =>
      rw [show (Int.ofNat x >>> 1) = Int.ofNat (x >>> 1) by rfl]
      change Nat.testBit x (i + 1) = Nat.testBit (x >>> 1) i
      simpa [Nat.shiftRight_eq_div_pow] using Nat.testBit_succ x i
  | negSucc x =>
      rw [show (Int.negSucc x >>> 1) = Int.negSucc (x >>> 1) by rfl]
      change Bool.not (Nat.testBit x (i + 1)) = Bool.not (Nat.testBit (x >>> 1) i)
      simpa [Nat.shiftRight_eq_div_pow] using congrArg Bool.not (Nat.testBit_succ x i)

private theorem add_testbit_zero_of_disjoint (x y : Int)
    (hxy : (Z.testbit x 0 && Z.testbit y 0) = false) :
    Z.testbit (x + y) 0 = (Z.testbit x 0 || Z.testbit y 0) := by
  have hmod := (div_mod_add_of_testbit_zero_disjoint x y hxy).2
  have hsum := modulo_two_eq_bit (x + y)
  have hx := modulo_two_eq_bit x
  have hy := modulo_two_eq_bit y
  rw [hmod, hx, hy] at hsum
  cases hbx : Z.testbit x 0 <;> cases hby : Z.testbit y 0 <;>
    simp [hbx, hby] at hxy hsum ⊢ <;> assumption

private theorem Z_add_is_or_nat (i : Nat) (x y : Int)
    (hxy : forall j : Nat, j <= i ->
      (Z.testbit x (Int.ofNat j) && Z.testbit y (Int.ofNat j)) = false) :
    Z.testbit (x + y) (Int.ofNat i) =
      (Z.testbit x (Int.ofNat i) || Z.testbit y (Int.ofNat i)) := by
  induction i generalizing x y with
  | zero =>
      exact add_testbit_zero_of_disjoint x y (hxy 0 (by omega))
  | succ i ih =>
      have hzero := hxy 0 (by omega)
      have hdiv := (div_mod_add_of_testbit_zero_disjoint x y hzero).1
      rw [testbit_succ_div_two, hdiv]
      have hnext : forall j : Nat, j <= i ->
          (Z.testbit (Z.div x 2) (Int.ofNat j) &&
            Z.testbit (Z.div y 2) (Int.ofNat j)) = false := by
        intro j hj
        rw [← testbit_succ_div_two, ← testbit_succ_div_two]
        exact hxy (j + 1) (by omega)
      rw [ih (Z.div x 2) (Z.div y 2) hnext]
      rw [← testbit_succ_div_two, ← testbit_succ_div_two]

theorem Z_add_is_or (i : Int) (hi : 0 <= i) (x y : Int)
    (hxy : forall j : Int, 0 <= j ∧ j <= i ->
      (Z.testbit x j && Z.testbit y j) = false) :
    Z.testbit (x + y) i = (Z.testbit x i || Z.testbit y i) := by
  cases i with
  | negSucc i => omega
  | ofNat i =>
      apply Z_add_is_or_nat i x y
      intro j hj
      exact hxy (Int.ofNat j) ⟨Int.ofNat_zero_le j, Int.ofNat_le.mpr hj⟩

theorem Zquot_Zdiv (x y : Int) (hy : y > 0) :
    Z.quot x y = if x < 0 then Z.div (x + y - 1) y else Z.div x y := by
  unfold Z.quot Z.div
  split
  · rename_i hx
    let r := x.fmod y
    let q := x.fdiv y
    have hy0 : 0 <= y := by omega
    have hr0 : 0 <= r := by
      exact Int.fmod_nonneg_of_pos x hy
    have hry : r < y := by
      exact Int.fmod_lt_of_pos x hy
    have hdecomp : r + y * q = x := by
      simpa [r, q] using Int.fmod_add_mul_fdiv x y
    have hshift : x + y - 1 = (r - 1) + (q + 1) * y := by
      rw [← hdecomp]
      grind
    rw [hshift, Int.add_mul_fdiv_right _ _ (by omega), Int.tdiv_eq_fdiv]
    have hsign : y.sign = 1 := Int.sign_eq_one_of_pos hy
    have hxn : ¬0 <= x := by omega
    have hdvd : y ∣ x ↔ r = 0 := by
      simpa [r] using (Int.dvd_iff_fmod_eq_zero (a := y) (b := x))
    by_cases hr : r = 0
    · have hd : y ∣ x := hdvd.mpr hr
      have hySmall : (y - 1).fdiv y = 0 := by
        rw [Int.fdiv_eq_ediv_of_nonneg (y - 1) (by omega)]
        exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
      have hnegOne : (-1 : Int).fdiv y = -1 := by
        rw [Int.fdiv_eq_ediv_of_nonneg (-1) hy0]
        exact Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by omega)
      simp [q, hd, hr, hnegOne] <;> omega
    · have hndvd : ¬y ∣ x := fun h => hr (hdvd.mp h)
      have hrPos : 0 < r := by omega
      have hsmall : (r - 1).fdiv y = 0 := by
        rw [Int.fdiv_eq_ediv_of_nonneg (r - 1) (by omega)]
        exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
      simp [q, hxn, hy0, hsign, hndvd, hsmall] <;> omega
  · rename_i hx
    exact (Int.fdiv_eq_tdiv_of_nonneg (by omega) (by omega)).symm

end Zbits

namespace Wordsize_8

def wordsize : Nat := 8

theorem wordsize_not_zero : Not (wordsize = 0) := by decide

end Wordsize_8

namespace Wordsize_32

def wordsize : Nat := 32

theorem wordsize_not_zero : Not (wordsize = 0) := by decide

end Wordsize_32

namespace Wordsize_64

def wordsize : Nat := 64

theorem wordsize_not_zero : Not (wordsize = 0) := by decide

end Wordsize_64

namespace Byte

def wordsize : Nat := Wordsize_8.wordsize
def zwordsize : Int := Int.ofNat wordsize
def modulus : Int := (2 : Int) ^ wordsize
def half_modulus : Int := modulus / 2
def max_unsigned : Int := modulus - 1
def max_signed : Int := half_modulus - 1
def min_signed : Int := -half_modulus
def cast_unsigned (z : Int) : Int := Z.modulo z modulus
def cast_signed (z : Int) : Int :=
  let x := cast_unsigned z
  if x < half_modulus then x else x - modulus
def eqm : Int -> Int -> Prop := Zbits.eqmod modulus

theorem eqm_refl (x : Int) : eqm x x :=
  Zbits.eqmod_refl modulus x

theorem eqm_refl2 (x y : Int) (h : x = y) : eqm x y :=
  Zbits.eqmod_refl2 modulus x y h

theorem eqm_sym (x y : Int) (h : eqm x y) : eqm y x :=
  Zbits.eqmod_sym modulus x y h

theorem eqm_trans (x y z : Int) (hxy : eqm x y) (hyz : eqm y z) : eqm x z :=
  Zbits.eqmod_trans modulus x y z hxy hyz

theorem eqm_mod_eq (x y : Int) (h : eqm x y) :
    Z.modulo x modulus = Z.modulo y modulus :=
  Zbits.eqmod_mod_eq modulus (by decide) x y h

structure int where
  intval : _root_.Int
  intrange : -1 < intval ∧ intval < modulus

namespace int

theorem ext {x y : int} (h : x.intval = y.intval) : x = y := by
  cases x
  cases y
  simp_all

end int

instance : DecidableEq int := fun x y =>
  if h : x.intval = y.intval then isTrue (int.ext h)
  else isFalse (fun hxy => h (congrArg int.intval hxy))

def unsigned (n : int) : _root_.Int := n.intval

def signed (n : int) : _root_.Int :=
  if unsigned n < half_modulus then unsigned n else unsigned n - modulus

def repr (x : _root_.Int) : int :=
  { intval := Z.modulo x modulus
    intrange := by
      unfold Z.modulo
      constructor
      · have := _root_.Int.fmod_nonneg_of_pos x (by decide : (0 : _root_.Int) < modulus)
        omega
      · exact _root_.Int.fmod_lt_of_pos x (by decide) }

theorem unsigned_range (i : int) : 0 <= unsigned i ∧ unsigned i < modulus := by
  have hlo := i.intrange.1
  change -1 < unsigned i at hlo
  exact ⟨by omega, i.intrange.2⟩

theorem signed_range (i : int) :
    min_signed <= signed i ∧ signed i <= max_signed := by
  have h := unsigned_range i
  have h' : 0 <= unsigned i ∧ unsigned i < 256 := by
    simpa [modulus, wordsize, Wordsize_8.wordsize] using h
  change -128 <= (if unsigned i < 128 then unsigned i else unsigned i - 256) ∧
    (if unsigned i < 128 then unsigned i else unsigned i - 256) <= 127
  split <;> omega

theorem eqm_signed_unsigned (i : int) : eqm (signed i) (unsigned i) := by
  unfold signed
  split
  · exact eqm_refl _
  · refine ⟨-1, ?_⟩
    unfold modulus wordsize Wordsize_8.wordsize
    omega

theorem eqm_signed_repr (z : _root_.Int) : eqm z (signed (repr z)) := by
  apply eqm_trans z (unsigned (repr z)) (signed (repr z))
  · exact Zbits.eqmod_mod modulus z
  · exact eqm_sym _ _ (eqm_signed_unsigned (repr z))

end Byte

namespace Int

def wordsize : Nat := Wordsize_32.wordsize
def zwordsize : Int := Int.ofNat wordsize
def modulus : Int := (2 : Int) ^ wordsize
def half_modulus : Int := modulus / 2
def max_unsigned : Int := modulus - 1
def max_signed : Int := half_modulus - 1
def min_signed : Int := -half_modulus
def cast_unsigned (z : Int) : Int := Z.modulo z modulus
def cast_signed (z : Int) : Int :=
  let x := cast_unsigned z
  if x < half_modulus then x else x - modulus
def eqm : Int -> Int -> Prop := Zbits.eqmod modulus

theorem eqm_refl (x : Int) : eqm x x :=
  Zbits.eqmod_refl modulus x

theorem eqm_refl2 (x y : Int) (h : x = y) : eqm x y :=
  Zbits.eqmod_refl2 modulus x y h

theorem eqm_sym (x y : Int) (h : eqm x y) : eqm y x :=
  Zbits.eqmod_sym modulus x y h

theorem eqm_trans (x y z : Int) (hxy : eqm x y) (hyz : eqm y z) : eqm x z :=
  Zbits.eqmod_trans modulus x y z hxy hyz

theorem eqm_mod_eq (x y : Int) (h : eqm x y) :
    Z.modulo x modulus = Z.modulo y modulus :=
  Zbits.eqmod_mod_eq modulus (by decide) x y h

end Int

namespace Int64

def wordsize : Nat := Wordsize_64.wordsize
def zwordsize : Int := Int.ofNat wordsize
def modulus : Int := (2 : Int) ^ wordsize
def half_modulus : Int := modulus / 2
def max_unsigned : Int := modulus - 1
def max_signed : Int := half_modulus - 1
def min_signed : Int := -half_modulus
def cast_unsigned (z : Int) : Int := Z.modulo z modulus
def cast_signed (z : Int) : Int :=
  let x := cast_unsigned z
  if x < half_modulus then x else x - modulus
def eqm : Int -> Int -> Prop := Zbits.eqmod modulus

theorem eqm_refl (x : Int) : eqm x x :=
  Zbits.eqmod_refl modulus x

theorem eqm_refl2 (x y : Int) (h : x = y) : eqm x y :=
  Zbits.eqmod_refl2 modulus x y h

theorem eqm_sym (x y : Int) (h : eqm x y) : eqm y x :=
  Zbits.eqmod_sym modulus x y h

theorem eqm_trans (x y z : Int) (hxy : eqm x y) (hyz : eqm y z) : eqm x z :=
  Zbits.eqmod_trans modulus x y z hxy hyz

theorem eqm_mod_eq (x y : Int) (h : eqm x y) :
    Z.modulo x modulus = Z.modulo y modulus :=
  Zbits.eqmod_mod_eq modulus (by decide) x y h

end Int64

namespace CompCert.Int64

abbrev wordsize := _root_.Int64.wordsize
abbrev zwordsize := _root_.Int64.zwordsize
abbrev modulus := _root_.Int64.modulus
abbrev half_modulus := _root_.Int64.half_modulus
abbrev max_unsigned := _root_.Int64.max_unsigned
abbrev max_signed := _root_.Int64.max_signed
abbrev min_signed := _root_.Int64.min_signed
abbrev eqm := _root_.Int64.eqm

theorem modulus_val : modulus = 18446744073709551616 := rfl
theorem half_modulus_val : half_modulus = 9223372036854775808 := rfl
theorem max_unsigned_val : max_unsigned = 18446744073709551615 := rfl
theorem max_signed_val : max_signed = 9223372036854775807 := rfl
theorem min_signed_val : min_signed = -9223372036854775808 := rfl

structure int where
  intval : _root_.Int
  intrange : -1 < intval ∧ intval < modulus

namespace int

theorem ext {x y : int} (h : x.intval = y.intval) : x = y := by
  cases x
  cases y
  simp_all

end int


instance : DecidableEq int := fun x y =>
  if h : x.intval = y.intval then isTrue (int.ext h)
  else isFalse (fun hxy => h (congrArg int.intval hxy))

def unsigned (n : int) : _root_.Int := n.intval

def signed (n : int) : _root_.Int :=
  if unsigned n < half_modulus then unsigned n else unsigned n - modulus

def repr (x : _root_.Int) : int :=
  { intval := Z.modulo x modulus
    intrange := by
      unfold Z.modulo
      constructor
      · have := _root_.Int.fmod_nonneg_of_pos x (by decide : (0 : _root_.Int) < modulus)
        omega
      · exact _root_.Int.fmod_lt_of_pos x (by decide) }

def zero : int := repr 0
def one : int := repr 1
def mone : int := repr (-1)
def iwordsize : int := repr zwordsize

def eq (x y : int) : Bool := decide (unsigned x = unsigned y)
def lt (x y : int) : Bool := decide (signed x < signed y)
def ltu (x y : int) : Bool := decide (unsigned x < unsigned y)
def neg (x : int) : int := repr (-unsigned x)
def add (x y : int) : int := repr (unsigned x + unsigned y)
def sub (x y : int) : int := repr (unsigned x - unsigned y)
def mul (x y : int) : int := repr (unsigned x * unsigned y)
def divs (x y : int) : int := repr (Z.quot (signed x) (signed y))
def mods (x y : int) : int := repr (Z.rem (signed x) (signed y))
def divu (x y : int) : int := repr (Z.div (unsigned x) (unsigned y))
def modu (x y : int) : int := repr (Z.modulo (unsigned x) (unsigned y))
def and (x y : int) : int := repr (Z.land (unsigned x) (unsigned y))
def or (x y : int) : int := repr (Z.lor (unsigned x) (unsigned y))
def xor (x y : int) : int := repr (Z.lxor (unsigned x) (unsigned y))
def shl (x y : int) : int := repr (Z.shiftl (unsigned x) (unsigned y))
def shru (x y : int) : int := repr (Z.shiftr (unsigned x) (unsigned y))
def shr (x y : int) : int := repr (Z.shiftr (signed x) (unsigned y))

def cmp (c : comparison) (x y : int) : Bool :=
  match c with
  | Ceq => eq x y
  | Cne => !(eq x y)
  | Clt => lt x y
  | Cle => !(lt y x)
  | Cgt => lt y x
  | Cge => !(lt x y)

def cmpu (c : comparison) (x y : int) : Bool :=
  match c with
  | Ceq => eq x y
  | Cne => !(eq x y)
  | Clt => ltu x y
  | Cle => !(ltu y x)
  | Cgt => ltu y x
  | Cge => !(ltu x y)

theorem unsigned_range (i : int) : 0 <= unsigned i ∧ unsigned i < modulus := by
  have hlo := i.intrange.1
  change -1 < unsigned i at hlo
  exact ⟨by omega, i.intrange.2⟩

theorem unsigned_range_2 (i : int) :
    0 <= unsigned i ∧ unsigned i <= max_unsigned := by
  have h := unsigned_range i
  constructor
  · exact h.1
  · rw [max_unsigned_val]
    rw [modulus_val] at h
    omega

theorem signed_range (i : int) :
    min_signed <= signed i ∧ signed i <= max_signed := by
  have h := unsigned_range i
  rw [modulus_val] at h
  rw [min_signed_val, max_signed_val]
  unfold signed
  rw [half_modulus_val, modulus_val]
  split <;> omega

theorem signed_eq_unsigned_of_lt (i : int) (h : unsigned i < half_modulus) :
    signed i = unsigned i := by
  unfold signed
  simp [h]

theorem eqm_signed_unsigned (i : int) : eqm (signed i) (unsigned i) := by
  unfold signed
  split
  · exact _root_.Int64.eqm_refl _
  · refine ⟨-1, ?_⟩
    simp [modulus, _root_.Int64.modulus, _root_.Int64.wordsize,
      Wordsize_64.wordsize]
    omega

theorem eqm_samerepr (x y : _root_.Int) (h : eqm x y) : repr x = repr y := by
  apply int.ext
  exact _root_.Int64.eqm_mod_eq x y h

theorem repr_unsigned (i : int) : repr (unsigned i) = i := by
  apply int.ext
  change Z.modulo (unsigned i) modulus = unsigned i
  unfold Z.modulo
  exact _root_.Int.fmod_eq_of_lt (unsigned_range i).1 (unsigned_range i).2

theorem repr_signed (i : int) : repr (signed i) = i := by
  apply int.ext
  change Z.modulo (signed i) modulus = unsigned i
  calc
    Z.modulo (signed i) modulus = Z.modulo (unsigned i) modulus := by
      simpa [modulus, _root_.Int64.modulus, _root_.Int64.wordsize,
        Wordsize_64.wordsize] using
        _root_.Int64.eqm_mod_eq _ _ (eqm_signed_unsigned i)
    _ = unsigned i := by
      unfold Z.modulo
      exact _root_.Int.fmod_eq_of_lt (unsigned_range i).1 (unsigned_range i).2

theorem unsigned_repr (z : _root_.Int)
    (h : 0 <= z ∧ z <= max_unsigned) : unsigned (repr z) = z := by
  change Z.modulo z modulus = z
  unfold Z.modulo
  apply _root_.Int.fmod_eq_of_lt h.1
  have hhi := h.2
  rw [max_unsigned_val] at hhi
  rw [modulus_val]
  omega

private theorem modulo_eq_add_modulus_of_neg (z : _root_.Int)
    (hz : min_signed <= z ∧ z < 0) : Z.modulo z modulus = z + modulus := by
  have hrange : 0 <= z + modulus ∧ z + modulus < modulus := by
    have hlo := hz.1
    rw [min_signed_val] at hlo
    rw [modulus_val]
    omega
  calc
    Z.modulo z modulus = Z.modulo ((z + modulus) + (-1) * modulus) modulus := by
      congr 1
      omega
    _ = Z.modulo (z + modulus) modulus := _root_.Int.add_mul_fmod_self_right _ _ _
    _ = z + modulus := _root_.Int.fmod_eq_of_lt hrange.1 hrange.2

theorem signed_repr (z : _root_.Int)
    (h : min_signed <= z ∧ z <= max_signed) : signed (repr z) = z := by
  change (if Z.modulo z modulus < half_modulus then Z.modulo z modulus
    else Z.modulo z modulus - modulus) = z
  by_cases hz : z < 0
  · have hmod := modulo_eq_add_modulus_of_neg z ⟨h.1, hz⟩
    rw [hmod]
    have hhalf : ¬z + modulus < half_modulus := by
      have hlo := h.1
      rw [min_signed_val] at hlo
      rw [modulus_val, half_modulus_val]
      omega
    simp [hhalf]
  · have hz0 : 0 <= z := by omega
    have hmod : Z.modulo z modulus = z := by
      unfold Z.modulo
      apply _root_.Int.fmod_eq_of_lt hz0
      have hhi := h.2
      rw [max_signed_val] at hhi
      rw [modulus_val]
      omega
    rw [hmod]
    have hhalf : z < half_modulus := by
      have hhi := h.2
      rw [max_signed_val] at hhi
      rw [half_modulus_val]
      omega
    simp [hhalf]

theorem unsigned_zero : unsigned zero = 0 := by native_decide
theorem unsigned_one : unsigned one = 1 := by native_decide
theorem unsigned_mone : unsigned mone = modulus - 1 := by native_decide
theorem signed_zero : signed zero = 0 := by native_decide
theorem signed_one : signed one = 1 := by native_decide
theorem signed_mone : signed mone = -1 := by native_decide
theorem eq_true (x : int) : eq x x = true := by simp [eq]

theorem add_signed (x y : int) : add x y = repr (signed x + signed y) := by
  apply eqm_samerepr
  rcases eqm_signed_unsigned x with ⟨kx, hkx⟩
  rcases eqm_signed_unsigned y with ⟨ky, hky⟩
  refine ⟨-(kx + ky), ?_⟩
  rw [hkx, hky]
  grind

theorem sub_signed (x y : int) : sub x y = repr (signed x - signed y) := by
  apply eqm_samerepr
  rcases eqm_signed_unsigned x with ⟨kx, hkx⟩
  rcases eqm_signed_unsigned y with ⟨ky, hky⟩
  refine ⟨-(kx - ky), ?_⟩
  rw [hkx, hky]
  grind

theorem mul_signed (x y : int) : mul x y = repr (signed x * signed y) := by
  apply eqm_samerepr
  rcases eqm_signed_unsigned x with ⟨kx, hkx⟩
  rcases eqm_signed_unsigned y with ⟨ky, hky⟩
  refine ⟨-(kx * ky * modulus + kx * unsigned y + ky * unsigned x), ?_⟩
  rw [hkx, hky]
  grind

theorem unsigned_add_no_overflow (x y : int)
    (h : 0 <= unsigned x + unsigned y ∧
      unsigned x + unsigned y <= max_unsigned) :
    unsigned (add x y) = unsigned x + unsigned y := by
  unfold add
  exact unsigned_repr _ h

theorem ltu_add_repr_of_ltu_repr (x : int) (a b c : _root_.Int)
    (h : ltu x (repr b) = true) (ha : 0 <= a) (hb : 0 <= b)
    (habc : b + a <= c) (hc : 0 <= c ∧ c <= max_unsigned) :
    ltu (add x (repr a)) (repr c) = true := by
  have hbRange : 0 <= b ∧ b <= max_unsigned := by omega
  have haRange : 0 <= a ∧ a <= max_unsigned := by omega
  have hUb := unsigned_repr b hbRange
  have hUa := unsigned_repr a haRange
  have hUc := unsigned_repr c hc
  have hx : unsigned x < b := by
    simpa [ltu, hUb] using h
  have hsum : 0 <= unsigned x + unsigned (repr a) ∧
      unsigned x + unsigned (repr a) <= max_unsigned := by
    rw [hUa]
    have hrange := unsigned_range x
    omega
  simp [ltu, unsigned_add_no_overflow x (repr a) hsum, hUa, hUc]
  omega

theorem sub_add_cancel (x y : int) : sub (add x y) y = x := by
  apply int.ext
  change Z.modulo (Z.modulo (unsigned x + unsigned y) modulus - unsigned y)
    modulus = unsigned x
  unfold Z.modulo
  rw [_root_.Int.sub_eq_add_neg, _root_.Int.fmod_add_fmod]
  have hrange := unsigned_range x
  rw [show unsigned x + unsigned y + -unsigned y = unsigned x by omega]
  exact _root_.Int.fmod_eq_of_lt hrange.1 hrange.2

theorem and_zero (x : int) : and x zero = zero := by
  apply int.ext
  change Z.modulo (Z.land (unsigned x) (unsigned zero)) modulus =
    Z.modulo 0 modulus
  rw [unsigned_zero]
  rw [Z.land_zero]

theorem and_zero_l (x : int) : and zero x = zero := by
  apply int.ext
  change Z.modulo (Z.land (unsigned zero) (unsigned x)) modulus =
    Z.modulo 0 modulus
  rw [unsigned_zero]
  rw [Z.zero_land]

end CompCert.Int64

namespace Int64

abbrev int := CompCert.Int64.int
abbrev unsigned := CompCert.Int64.unsigned
abbrev signed := CompCert.Int64.signed
abbrev repr := CompCert.Int64.repr
abbrev zero := CompCert.Int64.zero
abbrev one := CompCert.Int64.one
abbrev mone := CompCert.Int64.mone
abbrev iwordsize := CompCert.Int64.iwordsize
abbrev eq := CompCert.Int64.eq
abbrev ltu := CompCert.Int64.ltu
abbrev divs := CompCert.Int64.divs
abbrev mods := CompCert.Int64.mods
abbrev divu := CompCert.Int64.divu
abbrev modu := CompCert.Int64.modu
abbrev and := CompCert.Int64.and
abbrev or := CompCert.Int64.or
abbrev shl := CompCert.Int64.shl
abbrev shru := CompCert.Int64.shru
abbrev shr := CompCert.Int64.shr
abbrev cmp := CompCert.Int64.cmp
abbrev cmpu := CompCert.Int64.cmpu
abbrev unsigned_range := CompCert.Int64.unsigned_range
abbrev unsigned_range_2 := CompCert.Int64.unsigned_range_2
abbrev signed_range := CompCert.Int64.signed_range
abbrev signed_eq_unsigned_of_lt := CompCert.Int64.signed_eq_unsigned_of_lt
abbrev eqm_signed_unsigned := CompCert.Int64.eqm_signed_unsigned
abbrev eqm_samerepr := CompCert.Int64.eqm_samerepr
abbrev repr_unsigned := CompCert.Int64.repr_unsigned
abbrev repr_signed := CompCert.Int64.repr_signed
abbrev unsigned_repr := CompCert.Int64.unsigned_repr
abbrev signed_repr := CompCert.Int64.signed_repr
abbrev unsigned_zero := CompCert.Int64.unsigned_zero
abbrev unsigned_one := CompCert.Int64.unsigned_one
abbrev unsigned_mone := CompCert.Int64.unsigned_mone
abbrev signed_zero := CompCert.Int64.signed_zero
abbrev signed_one := CompCert.Int64.signed_one
abbrev signed_mone := CompCert.Int64.signed_mone
abbrev eq_true := CompCert.Int64.eq_true
abbrev add_signed := CompCert.Int64.add_signed
abbrev sub_signed := CompCert.Int64.sub_signed
abbrev mul_signed := CompCert.Int64.mul_signed
abbrev unsigned_add_no_overflow := CompCert.Int64.unsigned_add_no_overflow
abbrev ltu_add_repr_of_ltu_repr := CompCert.Int64.ltu_add_repr_of_ltu_repr
abbrev and_zero_l := CompCert.Int64.and_zero_l

end Int64
