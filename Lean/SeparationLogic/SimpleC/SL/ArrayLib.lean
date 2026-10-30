import SimpleC.SL.ArrayLibCore

namespace SimpleC.SL.ArrayLib

open SimpleC.SL.ArrayLibCore
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CArch
open SimpleC.SL.CNotation
open SimpleC.SL.FloatLib
open SimpleC.SL.Mem
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932

structure ArrayLibSig
    (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
    extends ArrayLibCoreSig Arch Endian CRules DePredSig SLibSig where

namespace ArrayLibSig

def canonical (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayLibSig Arch Endian CRules DePredSig SLibSig :=
  ⟨ArrayLibCoreSig.canonical Arch Endian CRules DePredSig SLibSig⟩

private abbrev mkElementStore {A : Type}
    (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
    (stride size : Int) (hsize : size = stride)
    (store : SimpleC.SL.Mem.addr -> A -> CRules.expr)
    (undefstore : SimpleC.SL.Mem.addr -> CRules.expr)
    (hforget : forall p a, CRules.derivable1 (store p a) (undefstore p))
    (hstoreAlign : forall p a,
      CRules.derivable1 (store p a) (store_align_n Arch CRules size))
    (hundefAlign : forall p,
      CRules.derivable1 (undefstore p) (store_align_n Arch CRules size))
    (hvalid : 0 < size ∧ size < Int.max_unsigned) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig where
  A := A
  sizeA := size
  storeA := fun x lo a => store (x + lo * stride) a
  undefstoreA := fun x lo => undefstore (x + lo * stride)
  store_to_undefstore := by
    intro x lo a
    exact hforget (x + lo * stride) a
  storeA_shift := by
    intro x n lo a
    rw [hsize]
    have haddr : x + n * stride + lo * stride =
        x + (lo + n) * stride := by
      calc
        x + n * stride + lo * stride =
            x + (n * stride + lo * stride) := Int.add_assoc _ _ _
        _ = x + (lo * stride + n * stride) :=
          congrArg (fun z : Int => x + z)
            (Int.add_comm (n * stride) (lo * stride))
        _ = x + (lo + n) * stride := by rw [Int.add_mul]
    rw [haddr]
    exact CRules.toContext.logic_equiv_refl _
  undefstoreA_shift := by
    intro x n lo
    rw [hsize]
    have haddr : x + n * stride + lo * stride =
        x + (lo + n) * stride := by
      calc
        x + n * stride + lo * stride =
            x + (n * stride + lo * stride) := Int.add_assoc _ _ _
        _ = x + (lo * stride + n * stride) :=
          congrArg (fun z : Int => x + z)
            (Int.add_comm (n * stride) (lo * stride))
        _ = x + (lo + n) * stride := by rw [Int.add_mul]
    rw [haddr]
    exact CRules.toContext.logic_equiv_refl _
  store_to_align := by
    intro x lo a
    exact hstoreAlign (x + lo * stride) a
  undefstore_to_align := by
    intro x lo
    exact hundefAlign (x + lo * stride)
  sizeA_valid := hvalid

private theorem store_align4_as_align
    (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig) (p a size blocks : Int)
    (hsize : size = 4 * blocks)
    (hstore : CRules.derivable1 (store_int Arch Endian CRules p a)
      (store_align4_n Arch CRules blocks)) :
    CRules.derivable1 (store_int Arch Endian CRules p a) (store_align_n Arch CRules size) := by
  have h := CRules.toContext.derivable1_trans _ _ _ hstore
    (store_align4_to_store_align (Arch := Arch) CRules blocks)
  rw [hsize]
  exact h

private theorem undef_align4_as_align
    (Arch : CArchSig) (CRules : SeparationLogicSig)
    (P : CRules.expr) (size blocks : Int)
    (hsize : size = 4 * blocks)
    (hstore : CRules.derivable1 P (store_align4_n Arch CRules blocks)) :
    CRules.derivable1 P (store_align_n Arch CRules size) := by
  have h := CRules.toContext.derivable1_trans _ _ _ hstore
    (store_align4_to_store_align (Arch := Arch) CRules blocks)
  rw [hsize]
  exact h

noncomputable abbrev StoreBoolAsElement (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_bool) (sizeof_front_end_type Arch FET_bool) rfl
    (store_bool Arch CRules) (undef_store_bool Arch CRules)
    (store_bool_undef_store_bool (Arch := Arch) CRules)
    (by intro p a; simpa [DerivedPredSig.sizeof_bool Arch] using store_bool_align CRules p a)
    (by intro p; simpa [DerivedPredSig.sizeof_bool Arch] using undef_store_bool_align CRules p)
    (by rw [DerivedPredSig.sizeof_bool Arch]; constructor <;> decide)

noncomputable abbrev StoreCharAsElement (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_char) (sizeof_front_end_type Arch FET_char) rfl
    (store_char Arch CRules) (undef_store_char Arch CRules)
    (store_char_undef_store_char (Arch := Arch) CRules)
    (by intro p a; simpa [DerivedPredSig.sizeof_char Arch] using store_char_align CRules p a)
    (by intro p; simpa [DerivedPredSig.sizeof_char Arch] using undef_store_char_align CRules p)
    (by rw [DerivedPredSig.sizeof_char Arch]; constructor <;> decide)

noncomputable abbrev StoreUCharAsElement (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_uchar) (sizeof_front_end_type Arch FET_uchar) rfl
    (store_uchar Arch CRules) (undef_store_uchar Arch CRules)
    (store_uchar_undef_store_uchar (Arch := Arch) CRules)
    (by intro p a; simpa [DerivedPredSig.sizeof_uchar Arch] using store_uchar_align CRules p a)
    (by intro p; simpa [DerivedPredSig.sizeof_uchar Arch] using undef_store_uchar_align CRules p)
    (by rw [DerivedPredSig.sizeof_uchar Arch]; constructor <;> decide)

noncomputable abbrev StoreShortAsElement (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_short) (sizeof_front_end_type Arch FET_short) rfl
    (store_short Arch Endian CRules) (undef_store_short Arch CRules)
    (store_short_undef_store_short (Arch := Arch) (Endian := Endian) CRules)
    (by intro p a; simpa [DerivedPredSig.sizeof_short Arch] using store_short_align CRules p a)
    (by intro p; simpa [DerivedPredSig.sizeof_short Arch] using undef_store_short_align CRules p)
    (by rw [DerivedPredSig.sizeof_short Arch]; constructor <;> decide)

noncomputable abbrev StoreUShortAsElement (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_ushort) (sizeof_front_end_type Arch FET_ushort) rfl
    (store_ushort Arch Endian CRules) (undef_store_ushort Arch CRules)
    (store_ushort_undef_store_ushort (Arch := Arch) (Endian := Endian) CRules)
    (by intro p a; simpa [DerivedPredSig.sizeof_ushort Arch] using store_ushort_align CRules p a)
    (by intro p; simpa [DerivedPredSig.sizeof_ushort Arch] using undef_store_ushort_align CRules p)
    (by rw [DerivedPredSig.sizeof_ushort Arch]; constructor <;> decide)

noncomputable abbrev StoreIntAsElement (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_int) (sizeof_front_end_type Arch FET_int) rfl
    (store_int Arch Endian CRules) (undef_store_int Arch CRules)
    (store_int_undef_store_int (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      apply undef_align4_as_align Arch CRules (store_int Arch Endian CRules p a) _ 1
      · rw [DerivedPredSig.sizeof_int Arch]; decide
      · exact store_int_align4 CRules p a)
    (by
      intro p
      apply undef_align4_as_align Arch CRules (undef_store_int Arch CRules p) _ 1
      · rw [DerivedPredSig.sizeof_int Arch]; decide
      · exact undef_store_int_align4 CRules p)
    (by rw [DerivedPredSig.sizeof_int Arch]; constructor <;> decide)

noncomputable abbrev StoreUIntAsElement (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_uint) (sizeof_front_end_type Arch FET_uint) rfl
    (store_uint Arch Endian CRules) (undef_store_uint Arch CRules)
    (store_uint_undef_store_uint (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      apply undef_align4_as_align Arch CRules (store_uint Arch Endian CRules p a) _ 1
      · rw [DerivedPredSig.sizeof_uint Arch]; decide
      · exact store_uint_align4 CRules p a)
    (by
      intro p
      apply undef_align4_as_align Arch CRules (undef_store_uint Arch CRules p) _ 1
      · rw [DerivedPredSig.sizeof_uint Arch]; decide
      · exact undef_store_uint_align4 CRules p)
    (by rw [DerivedPredSig.sizeof_uint Arch]; constructor <;> decide)

noncomputable abbrev StoreInt64AsElement (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_int64) (sizeof_front_end_type Arch FET_int64) rfl
    (store_int64 Arch Endian CRules) (undef_store_int64 Arch CRules)
    (store_int64_undef_store_int64 (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      apply undef_align4_as_align Arch CRules (store_int64 Arch Endian CRules p a) _ 2
      · rw [DerivedPredSig.sizeof_int64 Arch]; decide
      · exact store_int64_align4 CRules p a)
    (by
      intro p
      apply undef_align4_as_align Arch CRules (undef_store_int64 Arch CRules p) _ 2
      · rw [DerivedPredSig.sizeof_int64 Arch]; decide
      · exact undef_store_int64_align4 CRules p)
    (by rw [DerivedPredSig.sizeof_int64 Arch]; constructor <;> decide)

noncomputable abbrev StoreUInt64AsElement (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_uint64) (sizeof_front_end_type Arch FET_uint64) rfl
    (store_uint64 Arch Endian CRules) (undef_store_uint64 Arch CRules)
    (store_uint64_undef_store_uint64 (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      apply undef_align4_as_align Arch CRules (store_uint64 Arch Endian CRules p a) _ 2
      · rw [DerivedPredSig.sizeof_uint64 Arch]; decide
      · exact store_uint64_align4 CRules p a)
    (by
      intro p
      apply undef_align4_as_align Arch CRules (undef_store_uint64 Arch CRules p) _ 2
      · rw [DerivedPredSig.sizeof_uint64 Arch]; decide
      · exact undef_store_uint64_align4 CRules p)
    (by rw [DerivedPredSig.sizeof_uint64 Arch]; constructor <;> decide)

noncomputable abbrev StoreInt128AsElement (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_int128) (sizeof_front_end_type Arch FET_int128) rfl
    (store_int128 Arch Endian CRules) (undef_store_int128 Arch CRules)
    (store_int128_undef_store_int128 (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      simpa [DerivedPredSig.sizeof_int128 Arch] using
        store_int128_align (Arch := Arch) (Endian := Endian) CRules p a)
    (by
      intro p
      simpa [DerivedPredSig.sizeof_int128 Arch] using
        undef_store_int128_align (Arch := Arch) CRules p)
    (by rw [DerivedPredSig.sizeof_int128 Arch]; constructor <;> decide)

noncomputable abbrev StoreUInt128AsElement (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_uint128) (sizeof_front_end_type Arch FET_uint128) rfl
    (store_uint128 Arch Endian CRules) (undef_store_uint128 Arch CRules)
    (store_uint128_undef_store_uint128 (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      simpa [DerivedPredSig.sizeof_uint128 Arch] using
        store_uint128_align (Arch := Arch) (Endian := Endian) CRules p a)
    (by
      intro p
      simpa [DerivedPredSig.sizeof_uint128 Arch] using
        undef_store_uint128_align (Arch := Arch) CRules p)
    (by rw [DerivedPredSig.sizeof_uint128 Arch]; constructor <;> decide)

noncomputable abbrev StorePtrAsElement (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    Arch.ptr_size_Z Arch.ptr_size_Z rfl
    (store_ptr Arch Endian CRules) (undef_store_ptr Arch CRules)
    (store_ptr_undef_store_ptr (Arch := Arch) (Endian := Endian) CRules)
    (store_ptr_align (Arch := Arch) (Endian := Endian) CRules)
    (undef_store_ptr_align (Arch := Arch) CRules)
    (by
      rcases Arch.ptr_size_32_or_64 with h | h
      · simp [CArchSig.ptr_size_Z, h, Int.max_unsigned, Int.modulus,
          Int.wordsize, Wordsize_32.wordsize]
      · simp [CArchSig.ptr_size_Z, h, Int.max_unsigned, Int.modulus,
          Int.wordsize, Wordsize_32.wordsize])

noncomputable def StoreFloatAsElement (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_float) (sizeof_front_end_type Arch FET_float) rfl
    (store_float Arch Endian CRules) (undef_store_float Arch CRules)
    (store_float_undef_store_float (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      simpa [DerivedPredSig.sizeof_float Arch] using
        store_float_align (Arch := Arch) (Endian := Endian) CRules p a)
    (by
      intro p
      apply undef_align4_as_align Arch CRules (undef_store_float Arch CRules p) _ 1
      · rw [DerivedPredSig.sizeof_float Arch]
        decide
      · exact undef_store_float_align4 (Arch := Arch) CRules p)
    (by rw [DerivedPredSig.sizeof_float Arch]; constructor <;> decide)

noncomputable def StoreDoubleAsElement (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_double) (sizeof_front_end_type Arch FET_double) rfl
    (store_double Arch Endian CRules) (undef_store_double Arch CRules)
    (store_double_undef_store_double (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      simpa [DerivedPredSig.sizeof_double Arch] using
        store_double_align (Arch := Arch) (Endian := Endian) CRules p a)
    (by
      intro p
      apply undef_align4_as_align Arch CRules (undef_store_double Arch CRules p) _ 2
      · rw [DerivedPredSig.sizeof_double Arch]
        decide
      · exact undef_store_double_align4 (Arch := Arch) CRules p)
    (by rw [DerivedPredSig.sizeof_double Arch]; constructor <;> decide)

noncomputable def StoreLongDoubleAsElement (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_long_double)
    (sizeof_front_end_type Arch FET_long_double) rfl
    (store_long_double Arch Endian CRules) (undef_store_long_double Arch CRules)
    (store_long_double_undef_store_long_double (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      simpa [DerivedPredSig.sizeof_long_double Arch] using
        store_long_double_align (Arch := Arch) (Endian := Endian) CRules p a)
    (by
      intro p
      simpa [DerivedPredSig.sizeof_long_double Arch] using
        undef_store_long_double_align (Arch := Arch) CRules p)
    (by rw [DerivedPredSig.sizeof_long_double Arch]; constructor <;> decide)

noncomputable def StoreFiniteFloatAsElement (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_float) (sizeof_front_end_type Arch FET_float) rfl
    (store_finite_float Arch Endian CRules) (undef_store_finite_float Arch CRules)
    (store_finite_float_undef_store_finite_float (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      simpa [DerivedPredSig.sizeof_float Arch] using
        store_finite_float_align (Arch := Arch) (Endian := Endian) CRules p a)
    (by
      intro p
      apply undef_align4_as_align Arch CRules (undef_store_finite_float Arch CRules p) _ 1
      · rw [DerivedPredSig.sizeof_float Arch]
        decide
      · exact undef_store_float_align4 (Arch := Arch) CRules p)
    (by rw [DerivedPredSig.sizeof_float Arch]; constructor <;> decide)

noncomputable def StoreFiniteDoubleAsElement (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_double) (sizeof_front_end_type Arch FET_double) rfl
    (store_finite_double Arch Endian CRules) (undef_store_finite_double Arch CRules)
    (store_finite_double_undef_store_finite_double (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      simpa [DerivedPredSig.sizeof_double Arch] using
        store_finite_double_align (Arch := Arch) (Endian := Endian) CRules p a)
    (by
      intro p
      apply undef_align4_as_align Arch CRules (undef_store_finite_double Arch CRules p) _ 2
      · rw [DerivedPredSig.sizeof_double Arch]
        decide
      · exact undef_store_double_align4 (Arch := Arch) CRules p)
    (by rw [DerivedPredSig.sizeof_double Arch]; constructor <;> decide)

noncomputable def StoreFiniteLongDoubleAsElement (Arch : CArchSig)
    (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ELEMENT_STORE Arch Endian CRules DePredSig SLibSig :=
  mkElementStore Arch Endian CRules DePredSig SLibSig
    (sizeof_front_end_type Arch FET_long_double)
    (sizeof_front_end_type Arch FET_long_double) rfl
    (store_finite_long_double Arch Endian CRules)
    (undef_store_finite_long_double Arch CRules)
    (store_finite_long_double_undef_store_finite_long_double
      (Arch := Arch) (Endian := Endian) CRules)
    (by
      intro p a
      simpa [DerivedPredSig.sizeof_long_double Arch] using
        store_finite_long_double_align (Arch := Arch) (Endian := Endian) CRules p a)
    (by
      intro p
      simpa [DerivedPredSig.sizeof_long_double Arch] using
        undef_store_long_double_align (Arch := Arch) CRules p)
    (by rw [DerivedPredSig.sizeof_long_double Arch]; constructor <;> decide)

structure ArrayFacade (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) where
  elementStore : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig

noncomputable abbrev BoolArray (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreBoolAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev CharArray (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreCharAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UCharArray (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUCharAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev ShortArray (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreShortAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UShortArray (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUShortAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev IntArray (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreIntAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UIntArray (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUIntAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev Int64Array (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreInt64AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UInt64Array (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUInt64AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev Int128Array (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreInt128AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UInt128Array (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUInt128AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev PtrArray (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StorePtrAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FloatArray (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFloatAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def DoubleArray (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def LongDoubleArray (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreLongDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FiniteFloatArray (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFiniteFloatAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FiniteDoubleArray (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFiniteDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FiniteLongDoubleArray (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    ArrayFacade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFiniteLongDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩


namespace ArrayFacade

variable {Arch : CArchSig} {Endian : CEndianSig}
variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig Arch Endian CRules}
variable {SLibSig : StoreLibSig Arch Endian CRules DePredSig}

abbrev A (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.A

abbrev sizeA (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.sizeA

abbrev storeA (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.storeA

abbrev undefstoreA (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.undefstoreA

abbrev mixedstoreA (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixedstoreA self.elementStore

abbrev seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg self.elementStore

abbrev missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i self.elementStore

abbrev full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full self.elementStore

abbrev undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg self.elementStore

abbrev undef_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i self.elementStore

abbrev undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full self.elementStore

abbrev seg_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape self.elementStore

abbrev missing_i_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape self.elementStore

abbrev full_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape self.elementStore

abbrev mixed_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg self.elementStore

abbrev mixed_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i self.elementStore

abbrev mixed_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full self.elementStore

abbrev seg_split_to_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_split_to_missing_i self.elementStore

abbrev full_split_to_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_split_to_missing_i self.elementStore

abbrev mixed_seg_split_to_mixed_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_split_to_mixed_missing_i self.elementStore

abbrev mixed_full_split_to_mixed_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_split_to_mixed_missing_i self.elementStore

abbrev missing_i_merge_to_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_merge_to_seg self.elementStore

abbrev missing_i_merge_to_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_merge_to_full self.elementStore

abbrev mixed_missing_i_merge_to_mixed_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_merge_to_mixed_seg self.elementStore

abbrev mixed_missing_i_merge_to_mixed_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_merge_to_mixed_full self.elementStore

abbrev undef_seg_split_to_undef_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_split_to_undef_missing_i self.elementStore

abbrev undef_full_split_to_undef_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_split_to_undef_missing_i self.elementStore

abbrev undef_missing_i_merge_to_undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_merge_to_undef_seg self.elementStore

abbrev undef_missing_i_merge_to_undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_merge_to_undef_full self.elementStore

abbrev mixed_seg_split_to_undef_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_split_to_undef_missing_i self.elementStore

abbrev mixed_full_split_to_undef_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_split_to_undef_missing_i self.elementStore

abbrev mixed_missing_i_merge_to_undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_merge_to_undef_seg self.elementStore

abbrev mixed_missing_i_merge_to_undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_merge_to_undef_full self.elementStore

abbrev seg_shape_split_to_missing_i_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_split_to_missing_i_shape self.elementStore

abbrev full_shape_split_to_missing_i_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_split_to_missing_i_shape self.elementStore

abbrev missing_i_shape_merge_to_seg_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_merge_to_seg_shape self.elementStore

abbrev missing_i_shape_merge_to_full_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_merge_to_full_shape self.elementStore

abbrev seg_split_to_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_split_to_seg self.elementStore

abbrev mixed_seg_split_to_mixed_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_split_to_mixed_seg self.elementStore

abbrev undef_seg_split_to_undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_split_to_undef_seg self.elementStore

abbrev seg_shape_split_to_seg_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_split_to_seg_shape self.elementStore

abbrev full_split_to_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_split_to_seg self.elementStore

abbrev mixed_full_split_to_mixed_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_split_to_mixed_seg self.elementStore

abbrev full_split_to_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_split_to_full self.elementStore

abbrev mixed_full_split_to_mixed_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_split_to_mixed_full self.elementStore

abbrev undef_full_split_to_undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_split_to_undef_seg self.elementStore

abbrev undef_full_split_to_undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_split_to_undef_full self.elementStore

abbrev full_shape_split_to_seg_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_split_to_seg_shape self.elementStore

abbrev full_shape_split_to_full_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_split_to_full_shape self.elementStore

abbrev seg_merge_to_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_merge_to_seg self.elementStore

abbrev mixed_seg_merge_to_mixed_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_merge_to_mixed_seg self.elementStore

abbrev undef_seg_merge_to_undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_merge_to_undef_seg self.elementStore

abbrev seg_shape_merge_to_seg_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_merge_to_seg_shape self.elementStore

abbrev seg_merge_to_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_merge_to_full self.elementStore

abbrev mixed_seg_merge_to_mixed_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_merge_to_mixed_full self.elementStore

abbrev undef_seg_merge_to_undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_merge_to_undef_full self.elementStore

abbrev seg_shape_merge_to_full_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_merge_to_full_shape self.elementStore

abbrev full_merge_to_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_merge_to_full self.elementStore

abbrev mixed_full_merge_to_mixed_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_merge_to_mixed_full self.elementStore

abbrev undef_full_merge_to_undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_merge_to_undef_full self.elementStore

abbrev full_shape_merge_to_full_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_merge_to_full_shape self.elementStore

abbrev full_to_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_seg self.elementStore

abbrev undef_full_to_undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_to_undef_seg self.elementStore

abbrev full_shape_to_seg_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_to_seg_shape self.elementStore

abbrev mixed_full_to_mixed_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_to_mixed_seg self.elementStore

abbrev seg_to_mixed_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_to_mixed_seg self.elementStore

abbrev full_to_mixed_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_mixed_seg self.elementStore

abbrev mixed_seg_to_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_to_seg self.elementStore

abbrev missing_i_to_mixed_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_to_mixed_missing_i self.elementStore

abbrev mixed_missing_i_to_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_to_missing_i self.elementStore

abbrev undef_seg_to_mixed_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_to_mixed_seg self.elementStore

abbrev undef_full_to_mixed_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_to_mixed_seg self.elementStore

abbrev seg_shift (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shift self.elementStore

abbrev mixed_seg_shift (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_shift self.elementStore

abbrev seg_0_shift (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_0_shift self.elementStore

abbrev mixed_seg_0_shift (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_0_shift self.elementStore

abbrev undef_seg_shift (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_shift self.elementStore

abbrev undef_seg_0_shift (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_0_shift self.elementStore

abbrev seg_shape_shift (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_shift self.elementStore

abbrev seg_shape_0_shift (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_0_shift self.elementStore

abbrev seg_to_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_to_full self.elementStore

abbrev mixed_seg_to_mixed_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_to_mixed_full self.elementStore

abbrev mixed_full_to_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_to_full self.elementStore

abbrev full_to_mixed_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_mixed_full self.elementStore

abbrev undef_full_to_mixed_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_to_mixed_full self.elementStore

abbrev seg_to_undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_to_undef_seg self.elementStore

abbrev mixed_seg_to_undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_to_undef_seg self.elementStore

abbrev seg_to_seg_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_to_seg_shape self.elementStore

abbrev undef_seg_to_undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_to_undef_full self.elementStore

abbrev seg_shape_to_full_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_to_full_shape self.elementStore

abbrev missing_i_to_seg_head (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_to_seg_head self.elementStore

abbrev mixed_missing_i_to_mixed_seg_head (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_to_mixed_seg_head self.elementStore

abbrev undef_missing_i_to_undef_seg_head (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_to_undef_seg_head self.elementStore

abbrev missing_i_shape_to_seg_shape_head (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_to_seg_shape_head self.elementStore

abbrev missing_i_to_undef_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_to_undef_missing_i self.elementStore

abbrev mixed_missing_i_to_undef_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_to_undef_missing_i self.elementStore

abbrev undef_missing_i_to_mixed_missing_i (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_to_mixed_missing_i self.elementStore

abbrev missing_i_to_missing_i_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_to_missing_i_shape self.elementStore

abbrev full_to_undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_undef_full self.elementStore

abbrev mixed_seg_to_undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_to_undef_full self.elementStore

abbrev mixed_full_to_undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_to_undef_seg self.elementStore

abbrev mixed_full_to_undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_to_undef_full self.elementStore

abbrev full_to_full_shape (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_full_shape self.elementStore

abbrev missing_i_to_seg_tail (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_to_seg_tail self.elementStore

abbrev mixed_missing_i_to_mixed_seg_tail (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_to_mixed_seg_tail self.elementStore

abbrev undef_missing_i_to_undef_seg_tail (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_to_undef_seg_tail self.elementStore

abbrev missing_i_shape_to_seg_shape_tail (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_to_seg_shape_tail self.elementStore

abbrev seg_shape_to_undef_seg (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_to_undef_seg self.elementStore

abbrev full_shape_to_undef_full (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_to_undef_full self.elementStore

abbrev undef_seg_to_align (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_to_align self.elementStore

abbrev seg_to_align (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_to_align self.elementStore

abbrev mixed_seg_to_align (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_to_align self.elementStore

abbrev seg_shape_to_align (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_to_align self.elementStore

abbrev full_to_align (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_align self.elementStore

abbrev mixed_full_to_align (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_to_align self.elementStore

abbrev undef_full_to_align (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_to_align self.elementStore

abbrev full_shape_to_align (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_to_align self.elementStore

abbrev undef_full_valid (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_valid self.elementStore

abbrev full_shape_valid (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_valid self.elementStore

abbrev seg_length_range (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_length_range self.elementStore

abbrev mixed_seg_length_range (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_length_range self.elementStore

abbrev undef_seg_length_range (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_length_range self.elementStore

abbrev seg_shape_length_range (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_length_range self.elementStore

abbrev full_length_range (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_length_range self.elementStore

abbrev mixed_full_length_range (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_length_range self.elementStore

abbrev undef_full_length_range (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_length_range self.elementStore

abbrev full_shape_length_range (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_length_range self.elementStore

abbrev mixedstoreA_to_undefstoreA (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixedstoreA_to_undefstoreA self.elementStore

abbrev mixedstoreA_shift (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixedstoreA_shift self.elementStore

abbrev seg_length (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_length self.elementStore

abbrev seg_Zlength (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_Zlength self.elementStore

abbrev seg_nil (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_nil self.elementStore

abbrev seg_single (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_single self.elementStore

abbrev mixed_seg_single (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_single self.elementStore

abbrev undef_seg_single (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_single self.elementStore

abbrev seg_shape_single (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_single self.elementStore

abbrev full_length (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_length self.elementStore

abbrev full_Zlength (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_Zlength self.elementStore

abbrev mixed_seg_length (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_length self.elementStore

abbrev mixed_seg_Zlength (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_Zlength self.elementStore

abbrev mixed_seg_nil (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_nil self.elementStore

abbrev mixed_full_length (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_length self.elementStore

abbrev mixed_full_Zlength (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_Zlength self.elementStore

abbrev mixed_missing_i_length (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_length self.elementStore

abbrev mixed_missing_i_Zlength (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_Zlength self.elementStore

abbrev missing_i_length (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_length self.elementStore

abbrev missing_i_Zlength (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_Zlength self.elementStore

abbrev seg_valid (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_valid self.elementStore

abbrev mixed_seg_valid (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_valid self.elementStore

abbrev undef_seg_valid (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_valid self.elementStore

abbrev seg_shape_valid (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_valid self.elementStore

abbrev seg_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_empty self.elementStore

abbrev mixed_seg_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_empty self.elementStore

abbrev undef_seg_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_empty self.elementStore

abbrev seg_shape_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_empty self.elementStore

abbrev seg_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_unfold self.elementStore

abbrev mixed_seg_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_unfold self.elementStore

abbrev undef_seg_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_unfold self.elementStore

abbrev seg_shape_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_unfold self.elementStore

abbrev missing_i_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_empty self.elementStore

abbrev mixed_missing_i_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_empty self.elementStore

abbrev undef_missing_i_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_empty self.elementStore

abbrev missing_i_shape_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_empty self.elementStore

abbrev missing_i_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_unfold self.elementStore

abbrev mixed_missing_i_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_unfold self.elementStore

abbrev undef_missing_i_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_unfold self.elementStore

abbrev missing_i_shape_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_unfold self.elementStore

abbrev full_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_empty self.elementStore

abbrev mixed_full_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_empty self.elementStore

abbrev undef_full_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_empty self.elementStore

abbrev full_shape_empty (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_empty self.elementStore

abbrev full_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_unfold self.elementStore

abbrev mixed_full_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_unfold self.elementStore

abbrev undef_full_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_unfold self.elementStore

abbrev full_shape_unfold (self : ArrayFacade Arch Endian CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_unfold self.elementStore

end ArrayFacade


end ArrayLibSig

export ArrayLibSig
  (StoreBoolAsElement StoreCharAsElement StoreUCharAsElement StoreShortAsElement
    StoreUShortAsElement StoreIntAsElement StoreUIntAsElement
    StoreInt64AsElement StoreUInt64AsElement StoreInt128AsElement
    StoreUInt128AsElement StorePtrAsElement StoreFloatAsElement
    StoreDoubleAsElement StoreLongDoubleAsElement StoreFiniteFloatAsElement
    StoreFiniteDoubleAsElement StoreFiniteLongDoubleAsElement
    BoolArray CharArray UCharArray ShortArray UShortArray IntArray UIntArray
    Int64Array UInt64Array Int128Array UInt128Array PtrArray FloatArray
    DoubleArray LongDoubleArray FiniteFloatArray FiniteDoubleArray
    FiniteLongDoubleArray)

end SimpleC.SL.ArrayLib
