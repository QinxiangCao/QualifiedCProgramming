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
Require Export Array2LibCore.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type Array2LibSig
  (Arch : CArchSig)
  (Endian : CEndianSig)
  (CRules: SeparationLogicSig)
  (DePredSig : DerivedPredSig Arch Endian CRules)
  (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
  (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig).

Include Array2LibCoreSig Arch Endian CRules DePredSig SLibSig ALibSig.

Import CRules.
Import DePredSig.
Import SLibSig.
Import ALibSig.
Local Open Scope sac.

Module BoolArray2 := Array2Lib (StoreBoolAsElement).
Module CharArray2 := Array2Lib (StoreCharAsElement).
Module UCharArray2 := Array2Lib (StoreUCharAsElement).
Module ShortArray2 := Array2Lib (StoreShortAsElement).
Module UShortArray2 := Array2Lib (StoreUShortAsElement).
Module IntArray2 := Array2Lib (StoreIntAsElement).
Module UIntArray2 := Array2Lib (StoreUIntAsElement).
Module Int64Array2 := Array2Lib (StoreInt64AsElement).
Module UInt64Array2 := Array2Lib (StoreUInt64AsElement).
Module Int128Array2 := Array2Lib (StoreInt128AsElement).
Module UInt128Array2 := Array2Lib (StoreUInt128AsElement).
Module FloatArray2 := Array2Lib (StoreFloatAsElement).
Module DoubleArray2 := Array2Lib (StoreDoubleAsElement).
Module LongDoubleArray2 := Array2Lib (StoreLongDoubleAsElement).
Module FiniteFloatArray2 := Array2Lib (StoreFiniteFloatAsElement).
Module FiniteDoubleArray2 := Array2Lib (StoreFiniteDoubleAsElement).
Module FiniteLongDoubleArray2 := Array2Lib (StoreFiniteLongDoubleAsElement).
Module PtrArray2 := Array2Lib (StorePtrAsElement).

End Array2LibSig.
