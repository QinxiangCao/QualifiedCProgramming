import AUXLib.IntAuto

open AUXLib

#check min_signed_lt0
#check max_signed_gt0
#check zdiv_equiv
#check Zbits.Zquot_Zdiv
#check zadd_rm_head
#check zadd_rm_tail
#check zdiv_range_le_lt
#check zdiv_range_le_le
#check max_unsigned_gt0
#check max_unsigned_val
#check max_signed_val
#check min_signed_val
#check unsigned_mone_val
#check modulus_val
#check unsigned_inj
#check minus1lt
#check Z_land_range_lo
#check Z_land_range_lo_r
#check unsigned_zero
#check unsigned_one
#check eq_one_zero
#check eq_zero_zero
#check negb_true
#check negb_false
#check repr_zero
#check repr_one
#check and_zero_zero
#check and_one_zero
#check and_zero_one
#check and_one_one
#check or_zero_zero
#check or_one_zero
#check or_zero_one
#check or_one_one

-- Every source tactic entry point has a direct behavioral regression.
example (P : Prop) (f : True -> P) : P := by
  simpleproof

example : Int64.unsigned Int64.zero = 0 := by
  autorewritearith

example (c : Int) (x : Int64.int) (hc : c > 0) :
    Int64.min_signed <= Z.div (Int64.signed x) c := by
  solve_signed_range c x

example (c : Int) (x : Int64.int) (hc : c > 0) :
    0 <= Z.div (Int64.unsigned x) c := by
  solve_unsigned_range c x

example (c x : Int) (hc : c > 0)
    (hx : 0 <= x ∧ x < Int64.max_unsigned) :
    Z.div x c + 1 <= Int64.max_unsigned := by
  solve_unsigned_range_lt c x

example : Z.div 8 2 = 4 := by
  computedivmul
  rfl

example (x : Int) : Z.div 6 2 + x = x + 3 := by
  computedivmul
  omega

example (x y : Int) : Z.div x y = Z.div x y := by
  computedivmul
  rfl

example : Z.div (-5) (-2) = 2 := by
  computedivmul
  rfl

example (x : Int) : (6 : Int) * 7 + x = x + 42 := by
  computedivmul
  omega

example : True := by
  fail_if_success computedivmul
  trivial

example : True := by
  letI : HMul Int Int Int := ⟨fun _ _ => 99⟩
  have h : (2 : Int) * 3 = 99 ∧ Z.div 8 2 = 4 := by
    computedivmul
    fail_if_success computedivmul
    constructor <;> rfl
  trivial

example (x y : Int64.int) :
    Int64.min_signed <= Int64.signed x ∧
      Int64.unsigned y < Int64.modulus := by
  gen_signed_unsigned_range (Int64.signed x + Int64.unsigned y)
  simp only [Int64.signed, Int64.unsigned, min_signed_val, modulus_val]
  constructor <;> omega

example (x : Int64.int) : True := by
  gen_signed_unsigned_range (Int64.signed x)
  fail_if_success
    have : 0 <= Int64.unsigned x := by assumption
  trivial

example (x : Int64.int) : Int64.min_signed <= Int64.signed x := by
  solve_int_unequal

example (P : Prop) (h : P) (x : Int64.int)
    (hs : Int64.signed x < 0) : P := by
  solve_int_unequal
  exact h

example (x : Int64.int) :
    Int64.min_signed <= Int64.signed x ∧
      Int64.unsigned x <= Int64.max_unsigned := by
  solve_int_unequal

example : (5 : Int) <= Int64.max_unsigned := by
  unsigned_range

example : Int64.eq Int64.one Int64.zero = false := by
  int_auto_simpl

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  int_auto_simpl
  exact ⟨by assumption, by assumption⟩

example (P : Prop) (h : P) : P := by
  int_auto_simpl
  exact h

example (x y : Int64.int) :
    CompCert.Int64.add x y =
      Int64.repr (Int64.unsigned x + Int64.unsigned y) := by
  int_auto_simpl

example (z : Int) (hz : Int64.min_signed <= z ∧ z <= Int64.max_signed) :
    Int64.signed (Int64.repr z) = z := by
  int_auto_simpl

example (x y : Int64.int) (h : CompCert.Int64.lt x y = true) :
    Int64.signed x < Int64.signed y := by
  int_auto_simpl
  exact h

example (x y z : Int64.int) (h : CompCert.Int64.add x y = z) :
    Int64.repr (Int64.unsigned x + Int64.unsigned y) = z := by
  int_auto_H
  exact h

example (x y z : Int) (hx : x >= 0) (hy : y > 0)
    (h : Z.quot x y = z) : Z.div x y = z := by
  int_auto_H
  exact h

example (x y : Int) (hx : x >= 0) (hy : y > 0) :
    Z.quot x y = Z.div x y := by
  int_auto_H
  exact zdiv_equiv x y hx hy

example :
    CompCert.Int64.add (Int64.repr 1) (Int64.repr 2) = Int64.repr 3 := by
  int_auto'

example :
    CompCert.Int64.add (Int64.repr 1) (Int64.repr 2) = Int64.repr 3 := by
  int_auto

example :
    CompCert.Int64.add (Int64.repr 1) (Int64.repr 2) = Int64.repr 3 := by
  int auto

example (z1 z2 : Int)
    (h1 : 0 < z1 ∧ z1 < Int64.max_signed)
    (h2 : 0 < z2 ∧ z2 < Int64.max_signed)
    (h3 : z1 < z2) :
    CompCert.Int64.sub
      (CompCert.Int64.add (Int64.repr z1)
        (CompCert.Int64.sub (Int64.repr z2) (Int64.repr z1)))
      (CompCert.Int64.sub (Int64.repr z2) (Int64.repr z1)) = Int64.repr z1 := by
  int auto
  int auto
  int auto
  int auto

example (x y : Int)
    (hx : Int64.signed (Int64.repr 1) < x ∧ x < Int64.signed (Int64.repr 100))
    (hy : Int64.signed (Int64.repr 1) < y ∧ y < Int64.signed (Int64.repr 100)) :
    CompCert.Int64.add (Int64.repr x) (Int64.repr y) = Int64.repr (y + x) := by
  int auto

example (x y : Int) (hx : 1 < x ∧ x < Int64.signed (Int64.repr 100))
    (hy : 1 < y ∧ y < 100) :
    Int64.min_signed <= x + y ∧ x + y <= Int64.max_signed := by
  int auto

example (x y : Int) (hy : 0 < y ∧ y < x) (hx : x <= 1073741823) :
    Int64.signed (CompCert.Int64.add (Int64.repr x) (Int64.repr y)) = x + y := by
  int auto
  int auto

example (x : Int64.int) (h : Int64.ltu x (Int64.repr 100) = true) :
    Int64.ltu (CompCert.Int64.add x (Int64.repr 10)) (Int64.repr 120) = true := by
  int auto
  int auto

example (x : Int64.int) (h : Int64.signed x < 100) :
    Int64.min_signed <= Int64.signed x + 10 ∧
      Int64.signed x + 10 <= Int64.max_signed := by
  int auto

example (i1 i2 : Int64.int)
    (h0 : Int64.ltu Int64.zero i1 = true)
    (h12 : Int64.ltu i1 i2 = true) :
    CompCert.Int64.sub
      (CompCert.Int64.add i1 (CompCert.Int64.sub i2 i1))
      (CompCert.Int64.sub i2 i1) = i1 := by
  int auto
  int auto
  int auto
  int auto

example (i1 i2 : Int64.int)
    (h0 : Int64.ltu (Int64.repr 0) i1 = true)
    (hmax : Int64.ltu i2 (Int64.repr Int64.max_signed) = true)
    (h12 : Int64.ltu i1 i2 = true) : True := by
  fail_if_success
    have : Int64.unsigned (CompCert.Int64.sub i1 i2) < 1 := by
      int auto
      int auto
  trivial

#print axioms zdiv_range_le_le
#print axioms unsigned_inj
