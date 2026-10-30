import SimpleC.SL.PtrArray2LibCore

namespace SimpleC.SL.PtrArray2Lib

open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.ArrayLibCore
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CArch
open SimpleC.SL.PtrArray2LibCore
open SimpleC.SL.PtrArray2LibCore.PtrArray2LibCoreSig
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932

structure PtrArray2LibSig
    (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
    (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig)
    extends PtrArray2LibCoreSig Arch Endian CRules DePredSig SLibSig ALibSig where

namespace PtrArray2LibSig

def canonical (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
    (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig) :
    PtrArray2LibSig Arch Endian CRules DePredSig SLibSig ALibSig :=
  ⟨PtrArray2LibCoreSig.canonical Arch Endian CRules DePredSig SLibSig ALibSig⟩

structure PtrArray2Facade
    (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) where
  elementStore : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig

noncomputable abbrev BoolPtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    PtrArray2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreBoolAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev CharPtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    PtrArray2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreCharAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UCharPtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    PtrArray2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUCharAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev ShortPtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    PtrArray2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreShortAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UShortPtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    PtrArray2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUShortAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev IntPtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    PtrArray2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreIntAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UIntPtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    PtrArray2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUIntAsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev Int64PtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    PtrArray2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreInt64AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev UInt64PtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    PtrArray2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StoreUInt64AsElement Arch Endian CRules DePredSig SLibSig⟩

noncomputable abbrev PtrPtrArray2 (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig) :
    PtrArray2Facade Arch Endian CRules DePredSig SLibSig :=
  ⟨StorePtrAsElement Arch Endian CRules DePredSig SLibSig⟩

namespace PtrArray2Facade

variable {Arch : CArchSig} {Endian : CEndianSig}
variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig Arch Endian CRules}
variable {SLibSig : StoreLibSig Arch Endian CRules DePredSig}

abbrev A (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.A

abbrev sizeA (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.sizeA

abbrev storeA (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.storeA

abbrev undefstoreA (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  self.elementStore.undefstoreA

abbrev remove_Znth (_self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig)
    {B : Type} (i : Int) (l : List B) :=
  PtrArray2LibCoreSig.PtrArray2Lib.remove_Znth i l

abbrev replace_nth_decomp (_self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig)
    {B : Type} (n : Nat) (l : List B) (v : B) (h : n < l.length) :=
  PtrArray2LibCoreSig.PtrArray2Lib.replace_nth_decomp n l v h

abbrev replace_Znth_decomp (_self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig)
    {B : Type} (i : Int) (l : List B) (v : B)
    (h : 0 <= i ∧ i < AUXLib.Zlength l) :=
  PtrArray2LibCoreSig.PtrArray2Lib.replace_Znth_decomp i l v h

abbrev Znth_combine (_self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig)
    {B C : Type} (i : Int) (l1 : List B) (l2 : List C)
    (d1 : B) (d2 : C) (hi : 0 <= i ∧ i < AUXLib.Zlength l1)
    (hlen : AUXLib.Zlength l1 = AUXLib.Zlength l2) :=
  PtrArray2LibCoreSig.PtrArray2Lib.Znth_combine i l1 l2 d1 d2 hi hlen

abbrev combine_replace_Znth_r
    (_self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig)
    {B C : Type} (i : Int) (l1 : List B) (l2 : List C)
    (d1 : B) (v : C) (hi : 0 <= i ∧ i < AUXLib.Zlength l1)
    (hlen : AUXLib.Zlength l1 = AUXLib.Zlength l2) :=
  PtrArray2LibCoreSig.PtrArray2Lib.combine_replace_Znth_r
    i l1 l2 d1 v hi hlen

abbrev single_to_iter_sepcon
    (_self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.single_to_iter_sepcon CRules

abbrev iter_sepcon_split_remove_Znth
    (_self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig)
    {B : Type} (P : B -> CRules.expr) (i : Int) (l : List B) (d : B)
    (h : 0 <= i ∧ i < AUXLib.Zlength l) :=
  PtrArray2LibCoreSig.PtrArray2Lib.iter_sepcon_split_remove_Znth
    CRules P i l d h

abbrev iter_sepcon_merge_remove_Znth
    (_self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig)
    {B : Type} (P : B -> CRules.expr) (i : Int) (l : List B) (v : B)
    (h : 0 <= i ∧ i < AUXLib.Zlength l) :=
  PtrArray2LibCoreSig.PtrArray2Lib.iter_sepcon_merge_remove_Znth
    CRules P i l v h

abbrev row_block (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.row_block self.elementStore

abbrev mixed_row_block (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.mixed_row_block self.elementStore

abbrev row_blocks (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.row_blocks self.elementStore

abbrev mixed_row_blocks (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.mixed_row_blocks self.elementStore

abbrev row_blocks_missing_i
    (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.row_blocks_missing_i self.elementStore

abbrev mixed_row_blocks_missing_i
    (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.mixed_row_blocks_missing_i self.elementStore

abbrev full (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.full self.elementStore

abbrev missing_i (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.missing_i self.elementStore

abbrev mixed_full (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.mixed_full self.elementStore

abbrev mixed_missing_i (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.mixed_missing_i self.elementStore

abbrev undef_full (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.undef_full self.elementStore

abbrev full_Zlength (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.full_Zlength self.elementStore

abbrev mixed_full_Zlength (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.mixed_full_Zlength self.elementStore

abbrev undef_full_valid (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.undef_full_valid self.elementStore

abbrev Zlength_combine_eq
    (_self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig)
    {B C : Type} (l1 : List B) (l2 : List C)
    (h : AUXLib.Zlength l1 = AUXLib.Zlength l2) :=
  PtrArray2LibCoreSig.PtrArray2Lib.Zlength_combine_eq l1 l2 h

abbrev row_blocks_split_to_missing_i
    (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.row_blocks_split_to_missing_i
    self.elementStore

abbrev mixed_row_blocks_split_to_missing_i
    (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.mixed_row_blocks_split_to_missing_i
    self.elementStore

abbrev row_blocks_missing_i_merge_to_full
    (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.row_blocks_missing_i_merge_to_full
    self.elementStore

abbrev mixed_row_blocks_missing_i_merge_to_full
    (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.mixed_row_blocks_missing_i_merge_to_full
    self.elementStore

abbrev full_split_to_missing_i
    (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.full_split_to_missing_i self.elementStore

abbrev missing_i_merge_to_full
    (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.missing_i_merge_to_full self.elementStore

abbrev mixed_full_split_to_mixed_missing_i
    (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.mixed_full_split_to_mixed_missing_i
    self.elementStore

abbrev mixed_missing_i_merge_to_mixed_full
    (self : PtrArray2Facade Arch Endian CRules DePredSig SLibSig) :=
  PtrArray2LibCoreSig.PtrArray2Lib.mixed_missing_i_merge_to_mixed_full
    self.elementStore

end PtrArray2Facade

end PtrArray2LibSig

end SimpleC.SL.PtrArray2Lib
