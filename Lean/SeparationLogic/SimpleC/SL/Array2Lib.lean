import SimpleC.SL.Array2LibCore

namespace SimpleC.SL.Array2Lib

open SimpleC.SL.Array2LibCore
open SimpleC.SL.Array2LibCore.Array2LibCoreSig
open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932

structure Array2LibSig
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (ALibSig : ArrayLibSig CRules DePredSig SLibSig)
    extends Array2LibCoreSig CRules DePredSig SLibSig ALibSig where

namespace Array2LibSig

def canonical (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (ALibSig : ArrayLibSig CRules DePredSig SLibSig) :
    Array2LibSig CRules DePredSig SLibSig ALibSig :=
  ⟨Array2LibCoreSig.canonical CRules DePredSig SLibSig ALibSig⟩

structure Array2Facade
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) where
  elementStore : ELEMENT_STORE CRules DePredSig SLibSig

noncomputable def CharArray2 (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    Array2Facade CRules DePredSig SLibSig :=
  ⟨StoreCharAsElement CRules DePredSig SLibSig⟩

noncomputable def UCharArray2 (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    Array2Facade CRules DePredSig SLibSig :=
  ⟨StoreUCharAsElement CRules DePredSig SLibSig⟩

noncomputable def ShortArray2 (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    Array2Facade CRules DePredSig SLibSig :=
  ⟨StoreShortAsElement CRules DePredSig SLibSig⟩

noncomputable def UShortArray2 (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    Array2Facade CRules DePredSig SLibSig :=
  ⟨StoreUShortAsElement CRules DePredSig SLibSig⟩

noncomputable def IntArray2 (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    Array2Facade CRules DePredSig SLibSig :=
  ⟨StoreIntAsElement CRules DePredSig SLibSig⟩

noncomputable def UIntArray2 (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    Array2Facade CRules DePredSig SLibSig :=
  ⟨StoreUIntAsElement CRules DePredSig SLibSig⟩

noncomputable def Int64Array2 (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    Array2Facade CRules DePredSig SLibSig :=
  ⟨StoreInt64AsElement CRules DePredSig SLibSig⟩

noncomputable def UInt64Array2 (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    Array2Facade CRules DePredSig SLibSig :=
  ⟨StoreUInt64AsElement CRules DePredSig SLibSig⟩

noncomputable def PtrArray2 (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    Array2Facade CRules DePredSig SLibSig :=
  ⟨StorePtrAsElement CRules DePredSig SLibSig⟩

namespace Array2Facade

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : StoreLibSig CRules DePredSig}

abbrev A (self : Array2Facade CRules DePredSig SLibSig) :=
  self.elementStore.A

abbrev sizeA (self : Array2Facade CRules DePredSig SLibSig) :=
  self.elementStore.sizeA

abbrev storeA (self : Array2Facade CRules DePredSig SLibSig) :=
  self.elementStore.storeA

abbrev undefstoreA (self : Array2Facade CRules DePredSig SLibSig) :=
  self.elementStore.undefstoreA

abbrev row_addr (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.row_addr self.elementStore

abbrev row_store (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.row_store self.elementStore

abbrev mixed_row_store (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_row_store self.elementStore

abbrev undef_row_store (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.undef_row_store self.elementStore

abbrev full (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.full self.elementStore

abbrev missing_i (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.missing_i self.elementStore

abbrev mixed_full (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_full self.elementStore

abbrev mixed_missing_i (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_missing_i self.elementStore

abbrev undef_full (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.undef_full self.elementStore

abbrev undef_missing_i (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.undef_missing_i self.elementStore

abbrev full_Zlength (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.full_Zlength self.elementStore

abbrev mixed_full_Zlength (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_full_Zlength self.elementStore

abbrev missing_i_Zlength (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.missing_i_Zlength self.elementStore

abbrev mixed_missing_i_Zlength
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_missing_i_Zlength self.elementStore

abbrev full_valid (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.full_valid self.elementStore

abbrev mixed_full_valid (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_full_valid self.elementStore

abbrev row_store_to_undef_row_store
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.row_store_to_undef_row_store self.elementStore

abbrev mixed_row_store_to_undef_row_store
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_row_store_to_undef_row_store self.elementStore

abbrev full_split_to_missing_i
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.full_split_to_missing_i self.elementStore

abbrev missing_i_merge_to_full
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.missing_i_merge_to_full self.elementStore

abbrev mixed_full_split_to_mixed_missing_i
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_full_split_to_mixed_missing_i
    self.elementStore

abbrev mixed_missing_i_merge_to_mixed_full
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_missing_i_merge_to_mixed_full
    self.elementStore

abbrev undef_full_split_to_undef_missing_i
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.undef_full_split_to_undef_missing_i
    self.elementStore

abbrev full_to_undef_full
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.full_to_undef_full self.elementStore

abbrev mixed_full_to_undef_full
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.mixed_full_to_undef_full self.elementStore

abbrev undef_full_valid
    (self : Array2Facade CRules DePredSig SLibSig) :=
  Array2LibCoreSig.Array2Lib.undef_full_valid self.elementStore

end Array2Facade

end Array2LibSig

end SimpleC.SL.Array2Lib
