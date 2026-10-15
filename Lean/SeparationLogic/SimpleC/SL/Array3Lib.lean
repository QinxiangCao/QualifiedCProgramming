import SimpleC.SL.Array3LibCore

namespace SimpleC.SL.Array3Lib

open SimpleC.SL.Array2Lib
open SimpleC.SL.Array3LibCore
open SimpleC.SL.Array3LibCore.Array3LibCoreSig
open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932

structure Array3LibSig
    (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
    (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig)
    (A2LibSig : Array2LibSig Arch Endian CRules DePredSig SLibSig ALibSig)
    extends Array3LibCoreSig
      Arch Endian CRules DePredSig SLibSig ALibSig A2LibSig where

namespace Array3LibSig

def canonical (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
    (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig)
    (A2LibSig : Array2LibSig Arch Endian CRules DePredSig SLibSig ALibSig) :
    Array3LibSig Arch Endian CRules DePredSig SLibSig ALibSig A2LibSig :=
  ⟨Array3LibCoreSig.canonical
    Arch Endian CRules DePredSig SLibSig ALibSig A2LibSig⟩

structure Array3Facade
    (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) where
  elementStore : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig

noncomputable def CharArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreCharAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def UCharArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUCharAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def ShortArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreShortAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def UShortArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUShortAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def IntArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreIntAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def UIntArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUIntAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def Int64Array3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreInt64AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def UInt64Array3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUInt64AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def Int128Array3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreInt128AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def UInt128Array3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUInt128AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FloatArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFloatAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def DoubleArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def LongDoubleArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreLongDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FiniteFloatArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFiniteFloatAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FiniteDoubleArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFiniteDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def FiniteLongDoubleArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreFiniteLongDoubleAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable def PtrArray3 (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    Array3Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StorePtrAsElement Arch Endian CRules DePredSig SLibSig⟩

namespace Array3Facade

variable {Arch : CArchSig} {Endian : CEndianSig}
variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig Arch Endian CRules}
variable {SLibSig : StoreLibSig Arch Endian CRules DePredSig}

abbrev A (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.A

abbrev sizeA (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.sizeA

abbrev storeA (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.storeA

abbrev undefstoreA (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.undefstoreA

abbrev plane_addr (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.plane_addr self.elementStore

abbrev plane_store (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.plane_store self.elementStore

abbrev mixed_plane_store
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.mixed_plane_store self.elementStore

abbrev undef_plane_store
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.undef_plane_store self.elementStore

abbrev full (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.full self.elementStore

abbrev missing_i (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.missing_i self.elementStore

abbrev mixed_full (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.mixed_full self.elementStore

abbrev mixed_missing_i
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.mixed_missing_i self.elementStore

abbrev undef_full (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.undef_full self.elementStore

abbrev undef_missing_i
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.undef_missing_i self.elementStore

abbrev full_Zlength
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.full_Zlength self.elementStore

abbrev mixed_full_Zlength
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.mixed_full_Zlength self.elementStore

abbrev missing_i_Zlength
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.missing_i_Zlength self.elementStore

abbrev mixed_missing_i_Zlength
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.mixed_missing_i_Zlength self.elementStore

abbrev full_valid (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.full_valid self.elementStore

abbrev mixed_full_valid
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.mixed_full_valid self.elementStore

abbrev plane_store_to_undef_plane_store
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.plane_store_to_undef_plane_store self.elementStore

abbrev mixed_plane_store_to_undef_plane_store
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.mixed_plane_store_to_undef_plane_store self.elementStore

abbrev full_split_to_missing_i
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.full_split_to_missing_i self.elementStore

abbrev missing_i_merge_to_full
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.missing_i_merge_to_full self.elementStore

abbrev mixed_full_split_to_mixed_missing_i
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.mixed_full_split_to_mixed_missing_i self.elementStore

abbrev mixed_missing_i_merge_to_mixed_full
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.mixed_missing_i_merge_to_mixed_full self.elementStore

abbrev undef_full_split_to_undef_missing_i
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.undef_full_split_to_undef_missing_i self.elementStore

abbrev full_to_undef_full
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.full_to_undef_full self.elementStore

abbrev mixed_full_to_undef_full
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.mixed_full_to_undef_full self.elementStore

abbrev undef_full_valid
    (self : Array3Facade Arch Endian CRules DePredSig SLibSig) :=
  Array3LibCoreSig.Array3Lib.undef_full_valid self.elementStore

end Array3Facade

end Array3LibSig

end SimpleC.SL.Array3Lib
