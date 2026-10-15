import SimpleC.SL.CommonAssertion

namespace SimpleC.SL.StoreAux

open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig

/-- Lean counterpart of the parameterized Coq `StoreLibSig` module type. -/
structure StoreLibSig
    (_Arch : CArchSig)
    (_Endian : CEndianSig)
    (_CRules : SeparationLogicSig)
    (_DePredSig : DerivedPredSig _Arch _Endian _CRules) : Type where

namespace StoreLibSig

def canonical (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules) :
    StoreLibSig Arch Endian CRules DePredSig := {}

theorem store_byte_eqm (CRules : SeparationLogicSig)
    (p v v' : Int) (h : Byte.eqm v v') :
    CRules.derivable1
      (DerivedPredSig.store_byte CRules p v)
      (DerivedPredSig.store_byte CRules p v') :=
  CRules.mstore_eqm p v v' h

theorem eqm_iff_mod_eq (x y : Int) :
    Byte.eqm x y <-> Z.modulo x 256 = Z.modulo y 256 := by
  constructor
  · exact Byte.eqm_mod_eq x y
  · intro h
    apply Byte.eqm_trans x (Z.modulo x 256) y
    · exact Zbits.eqmod_mod 256 x
    · apply Byte.eqm_trans (Z.modulo x 256) (Z.modulo y 256) y
      · exact Byte.eqm_refl2 _ _ h
      · exact Byte.eqm_sym y (Z.modulo y 256) (Zbits.eqmod_mod 256 y)

theorem byte_eqm_unsigned_last_8 (x : Int) :
    Byte.eqm x (SimpleC.SL.IntLib.unsigned_last_nbits x 8) := by
  rw [eqm_iff_mod_eq]
  change Z.modulo x (Z.pow 2 8) =
    Z.modulo (SimpleC.SL.IntLib.unsigned_last_nbits x 8) (Z.pow 2 8)
  exact SimpleC.SL.IntLib.unsigned_Lastnbits_mod_correct x 8 (by omega)

theorem byte_eqm_signed_last_8 (x : Int) :
    Byte.eqm x (SimpleC.SL.IntLib.signed_last_nbits x 8) := by
  rw [eqm_iff_mod_eq]
  change Z.modulo x (Z.pow 2 8) =
    Z.modulo (SimpleC.SL.IntLib.signed_last_nbits x 8) (Z.pow 2 8)
  exact SimpleC.SL.IntLib.signed_Lastnbits_mod_correct x 8 (by omega)

-- Coq uses `Vector.cons` directly. These transparent aliases retain the
-- source-shaped vector surface without duplicating the CEndian implementation.
abbrev vector_cons {alpha : Type} {n : Nat}
    (x : alpha) (xs : Vector alpha n) : Vector alpha (n + 1) :=
  CArch.vector_cons x xs

abbrev vector_head {alpha : Type} {n : Nat} (xs : Vector alpha (n + 1)) : alpha :=
  CArch.vector_head xs

abbrev vector_tail {alpha : Type} {n : Nat}
    (xs : Vector alpha (n + 1)) : Vector alpha n :=
  CArch.vector_tail xs

theorem vector_head_cons {alpha : Type} {n : Nat}
    (x : alpha) (xs : Vector alpha n) : vector_head (vector_cons x xs) = x :=
  CArch.vector_head_cons x xs

theorem vector_tail_cons {alpha : Type} {n : Nat}
    (x : alpha) (xs : Vector alpha n) : vector_tail (vector_cons x xs) = xs :=
  CArch.vector_tail_cons x xs

theorem vector_cons_eta {alpha : Type} {n : Nat} (xs : Vector alpha (n + 1)) :
    vector_cons (vector_head xs) (vector_tail xs) = xs :=
  CArch.vector_cons_eta xs

abbrev bytes_eqm (Endian : CEndianSig) :
    (n : Nat) -> Vector Int n -> Vector Int n -> Prop :=
  DerivedPredSig.bytes_eqm Endian

abbrev n_bytes_to_Z (Endian : CEndianSig) :
    (n : Nat) -> Vector Int n -> Int :=
  DerivedPredSig.n_bytes_to_Z Endian

abbrev Z_to_n_bytes (Endian : CEndianSig) :
    Int -> (length : Nat) -> Vector Int length :=
  DerivedPredSig.Z_to_n_bytes Endian

abbrev merge_n_bytes (Endian : CEndianSig) :
    (n : Nat) -> Vector Int n -> Int -> Prop :=
  DerivedPredSig.merge_n_bytes Endian

theorem eqm_bytes_to_Z_eq (Endian : CEndianSig) (n : Nat)
    (v1 v2 : Vector Int n) (h : bytes_eqm Endian n v1 v2) :
    n_bytes_to_Z Endian n v1 = n_bytes_to_Z Endian n v2 :=
  Endian.eqm_bytes_to_Z_eq n v1 v2 h

theorem Z_to_n_bytes_to_Z (Endian : CEndianSig) (length : Nat) (v : Int) :
    n_bytes_to_Z Endian length (Z_to_n_bytes Endian v length) =
      Z.modulo v (Z.pow 2 (8 * Int.ofNat length)) :=
  Endian.Z_to_n_bytes_to_Z length v

theorem merge_short_equiv_merge_n_bytes (Endian : CEndianSig)
    (x1 x2 y : Int) :
    DerivedPredSig.merge_short Endian x1 x2 y <->
      merge_n_bytes Endian 2 (DerivedPredSig.vec2 x1 x2) y :=
  Endian.merge_short_equiv_merge_n_bytes x1 x2 y

theorem merge_int_equiv_merge_n_bytes (Endian : CEndianSig)
    (x1 x2 x3 x4 y : Int) :
    DerivedPredSig.merge_int Endian x1 x2 x3 x4 y <->
      merge_n_bytes Endian 4 (DerivedPredSig.vec4 x1 x2 x3 x4) y :=
  Endian.merge_int_equiv_merge_n_bytes x1 x2 x3 x4 y

theorem merge_int64_equiv_merge_n_bytes (Endian : CEndianSig)
    (x1 x2 x3 x4 x5 x6 x7 x8 y : Int) :
    DerivedPredSig.merge_int64 Endian x1 x2 x3 x4 x5 x6 x7 x8 y <->
      merge_n_bytes Endian 8
        (DerivedPredSig.vec8 x1 x2 x3 x4 x5 x6 x7 x8) y :=
  Endian.merge_int64_equiv_merge_n_bytes x1 x2 x3 x4 x5 x6 x7 x8 y

def store_n_bytes (_Arch : CArchSig) (_Endian : CEndianSig)
    (CRules : SeparationLogicSig) (x : Int) :
    (n : Nat) -> Vector Int n -> CRules.expr
  | 0, _ => CRules.emp
  | n + 1, v =>
      CRules.sepcon (CRules.mstore x (vector_head v))
        (store_n_bytes _Arch _Endian CRules (x + 1) n (vector_tail v))

def store_n_bytes_Z (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (x : Int) (n : Nat) (v : Int) : CRules.expr :=
  CRules.exp (Vector Int n) fun bytes =>
    CRules.andp
      (CRules.coq_prop (merge_n_bytes Endian n bytes v))
      (store_n_bytes Arch Endian CRules x n bytes)

def store_n_bytes_noninit (_Arch : CArchSig) (_Endian : CEndianSig)
    (CRules : SeparationLogicSig) (x : Int) :
    (n : Nat) -> Vector Int n -> CRules.expr
  | 0, _ => CRules.emp
  | n + 1, v =>
      CRules.sepcon (CRules.mstore_noninit x)
        (store_n_bytes_noninit _Arch _Endian CRules (x + 1) n (vector_tail v))

end StoreLibSig

/-- Legacy Arch32/BigEndian compatibility view retained for pre-parameterization
callers. Canonical P0-7/P0-8 code uses `StoreLibSig` explicitly; this is not a
second source semantics or a new Coq declaration. -/
abbrev StoreLibSigCompat (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSigCompat.Sig CRules) : Type :=
  StoreLibSig CArch.Arch32 CArch.BigEndian CRules DePredSig

namespace StoreLibSigCompat

def canonical (CRules : SeparationLogicSig) (DePredSig : DerivedPredSigCompat.Sig CRules) :
    StoreLibSigCompat CRules DePredSig :=
  StoreLibSig.canonical CArch.Arch32 CArch.BigEndian CRules DePredSig

abbrev n_bytes_to_Z_cons := CArch.BigEndian.n_bytes_to_Z_cons
abbrev Z_to_n_bytes_succ := CArch.BigEndian.Z_to_n_bytes_succ

end StoreLibSigCompat

end SimpleC.SL.StoreAux
