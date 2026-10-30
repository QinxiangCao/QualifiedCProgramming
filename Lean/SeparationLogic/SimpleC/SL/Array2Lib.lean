import SimpleC.SL.Array2LibCore

namespace SimpleC.SL.Array2Lib

open SimpleC.SL.Array2LibCore
open SimpleC.SL.Array2LibCore.Array2LibCoreSig
open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CArch
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932

structure Array2LibSig
    (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
    (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig)
    extends Array2LibCoreSig Arch Endian CRules DePredSig SLibSig ALibSig where

namespace Array2LibSig

def canonical (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
    (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig) :
    Array2LibSig Arch Endian CRules DePredSig SLibSig ALibSig :=
  ⟨Array2LibCoreSig.canonical Arch Endian CRules DePredSig SLibSig ALibSig⟩

structure Array2Facade
    (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) where
  elementStore : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig

noncomputable abbrev BoolArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreBoolAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev CharArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreCharAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UCharArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUCharAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev ShortArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreShortAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UShortArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUShortAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev IntArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreIntAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UIntArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUIntAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev Int64Array2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreInt64AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UInt64Array2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUInt64AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev Int128Array2 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreInt128AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UInt128Array2 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUInt128AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FloatArray2 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFloatAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def DoubleArray2 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def LongDoubleArray2 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreLongDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FiniteFloatArray2 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFiniteFloatAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FiniteDoubleArray2 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFiniteDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FiniteLongDoubleArray2 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFiniteLongDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev PtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StorePtrAsElement Arch Endian CRules DePredSig SLibSig⟩

namespace Array2Facade

variable {Arch : CArchSig} {Endian : CEndianSig}
variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig Arch Endian CRules}
variable {SLibSig : StoreLibSig Arch Endian CRules DePredSig}

abbrev A (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.A

abbrev sizeA (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.sizeA

abbrev storeA (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.storeA

abbrev undefstoreA (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.undefstoreA

abbrev row_addr (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.row_addr self.elementStore

abbrev row_store (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.row_store self.elementStore

abbrev mixed_row_store (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_row_store self.elementStore

abbrev undef_row_store (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.undef_row_store self.elementStore

abbrev full (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.full self.elementStore

abbrev missing_i (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.missing_i self.elementStore

abbrev mixed_full (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_full self.elementStore

abbrev mixed_missing_i (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_missing_i self.elementStore

abbrev undef_full (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.undef_full self.elementStore

abbrev undef_missing_i (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.undef_missing_i self.elementStore

abbrev full_Zlength (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.full_Zlength self.elementStore

abbrev mixed_full_Zlength (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_full_Zlength self.elementStore

abbrev missing_i_Zlength (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.missing_i_Zlength self.elementStore

abbrev mixed_missing_i_Zlength
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_missing_i_Zlength self.elementStore

abbrev full_valid (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.full_valid self.elementStore

abbrev mixed_full_valid (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_full_valid self.elementStore

abbrev row_store_to_undef_row_store
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.row_store_to_undef_row_store self.elementStore

abbrev mixed_row_store_to_undef_row_store
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_row_store_to_undef_row_store self.elementStore

abbrev full_split_to_missing_i
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.full_split_to_missing_i self.elementStore

abbrev missing_i_merge_to_full
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.missing_i_merge_to_full self.elementStore

abbrev mixed_full_split_to_mixed_missing_i
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_full_split_to_mixed_missing_i
    self.elementStore

abbrev mixed_missing_i_merge_to_mixed_full
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_missing_i_merge_to_mixed_full
    self.elementStore

abbrev undef_full_split_to_undef_missing_i
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.undef_full_split_to_undef_missing_i
    self.elementStore

abbrev full_to_undef_full
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.full_to_undef_full self.elementStore

abbrev mixed_full_to_undef_full
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_full_to_undef_full self.elementStore

abbrev undef_full_valid
    (self : Array2Facade Arch Endian CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.undef_full_valid self.elementStore

end Array2Facade

end Array2LibSig

end SimpleC.SL.Array2Lib
