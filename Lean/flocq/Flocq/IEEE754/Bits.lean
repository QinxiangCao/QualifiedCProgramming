import Flocq.IEEE754.Binary
import Lean.Elab.Tactic.Omega

namespace Flocq.IEEE754.Bits

open Flocq.IEEE754 Binary BinarySingleNaN

/-!
Lean migration of the FloatLib-reached encoding slice from
`flocq/src/IEEE754/Bits.v`.

Only declarations originating in `Bits.v` are defined here. The Lean-only
`BitVec` adapters live in `Flocq.Compatibility.IEEE`.
-/

abbrev binary32 : Type := binary_float 24 128
abbrev binary64 : Type := binary_float 53 1024

def bits_of_binary_float (mw ew : Int)
    (x : binary_float (mw + 1) ((2 : Int) ^ (ew - 1).toNat)) : Int :=
  BinaryFloat.bitsOf x

def binary_float_of_bits (mw ew : Int)
    (_ : 0 < mw) (_ : 0 < ew)
    (_ : mw + 1 < (2 : Int) ^ (ew - 1).toNat)
    (z : Int) : binary_float (mw + 1) ((2 : Int) ^ (ew - 1).toNat) :=
  BinaryFloat.ofBits _ z

def b32_of_bits (z : Int) : binary32 :=
  binary_float_of_bits 23 8 (by decide) (by decide) (by decide) z
def b64_of_bits (z : Int) : binary64 :=
  binary_float_of_bits 52 11 (by decide) (by decide) (by decide) z
def bits_of_b32 (x : binary32) : Int := bits_of_binary_float 23 8 x
def bits_of_b64 (x : binary64) : Int := bits_of_binary_float 52 11 x

theorem bits_of_binary_float_range (mw ew : Int) (_ : 0 < mw) (_ : 0 < ew)
    (x : binary_float (mw + 1) ((2 : Int) ^ (ew - 1).toNat)) :
    0 <= bits_of_binary_float mw ew x /\
      bits_of_binary_float mw ew x < (2 : Int) ^ (mw + ew + 1).toNat := by
  rename_i hmw hew
  constructor
  · exact BinaryFloat.bitsOf_nonneg x
  · have h := BinaryFloat.bitsOf_lt_modulus x
    have hwidth :
        (formatOfParameters (mw + 1) ((2 : Int) ^ (ew - 1).toNat)).width =
          (mw + ew + 1).toNat := by
      have hmw0 : 0 <= mw := le_of_lt hmw
      have hew0 : 0 <= ew := le_of_lt hew
      have hewm1 : (ew - 1).toNat + 1 = ew.toNat := by omega
      simp only [formatOfParameters, Flocq.Internal.IEEE.Format.width]
      simp only [show mw + 1 - 1 = mw by omega]
      have hpow : ((2 : Int) ^ (ew - 1).toNat).toNat =
          2 ^ (ew - 1).toNat := by norm_cast
      rw [hpow, Nat.log2_two_pow]
      omega
    rw [show (formatOfParameters (mw + 1) ((2 : Int) ^ (ew - 1).toNat)).modulus =
        2 ^ (mw + ew + 1).toNat by
      change 2 ^ (formatOfParameters (mw + 1)
        ((2 : Int) ^ (ew - 1).toNat)).width = 2 ^ (mw + ew + 1).toNat
      rw [hwidth]] at h
    norm_cast at h ⊢

end Flocq.IEEE754.Bits

namespace Flocq.IEEE754
export Bits
  (binary32 binary64 bits_of_binary_float binary_float_of_bits b32_of_bits
    b64_of_bits bits_of_b32 bits_of_b64 bits_of_binary_float_range)
end Flocq.IEEE754
