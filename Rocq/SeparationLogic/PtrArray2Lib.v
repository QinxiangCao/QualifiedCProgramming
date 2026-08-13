Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap ListLib.
From compcert.lib Require Import Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem CommonAssertion StoreAux ArrayLib.
Require Export PtrArray2LibCore.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type PtrArray2LibSig
  (Arch : CArchSig)
  (Endian : CEndianSig)
  (CRules: SeparationLogicSig)
  (DePredSig : DerivedPredSig Arch Endian CRules)
  (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
  (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig).

Include PtrArray2LibCoreSig Arch Endian CRules DePredSig SLibSig ALibSig.

Import CRules.
Import DePredSig.
Import SLibSig.
Import ALibSig.
Local Open Scope sac.

Module BoolPtrArray2 := PtrArray2Lib (StoreBoolAsElement).
Module CharPtrArray2 := PtrArray2Lib (StoreCharAsElement).
Module UCharPtrArray2 := PtrArray2Lib (StoreUCharAsElement).
Module ShortPtrArray2 := PtrArray2Lib (StoreShortAsElement).
Module UShortPtrArray2 := PtrArray2Lib (StoreUShortAsElement).
Module IntPtrArray2 := PtrArray2Lib (StoreIntAsElement).
Module UIntPtrArray2 := PtrArray2Lib (StoreUIntAsElement).
Module Int64PtrArray2 := PtrArray2Lib (StoreInt64AsElement).
Module UInt64PtrArray2 := PtrArray2Lib (StoreUInt64AsElement).
Module PtrPtrArray2 := PtrArray2Lib (StorePtrAsElement).

End PtrArray2LibSig.
