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
From SimpleC.SL Require Import Mem CommonAssertion StoreAux ArrayLib Array2Lib.
Require Export Array3LibCore.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type Array3LibSig
  (Arch : CArchSig)
  (Endian : CEndianSig)
  (CRules: SeparationLogicSig)
  (DePredSig : DerivedPredSig Arch Endian CRules)
  (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
  (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig)
  (A2LibSig : Array2LibSig Arch Endian CRules DePredSig SLibSig ALibSig).

Include Array3LibCoreSig Arch Endian CRules DePredSig SLibSig ALibSig A2LibSig.

Import CRules.
Import DePredSig.
Import SLibSig.
Import ALibSig.
Import A2LibSig.
Local Open Scope sac.

Module BoolArray3 := Array3Lib (StoreBoolAsElement).
Module CharArray3 := Array3Lib (StoreCharAsElement).
Module UCharArray3 := Array3Lib (StoreUCharAsElement).
Module ShortArray3 := Array3Lib (StoreShortAsElement).
Module UShortArray3 := Array3Lib (StoreUShortAsElement).
Module IntArray3 := Array3Lib (StoreIntAsElement).
Module UIntArray3 := Array3Lib (StoreUIntAsElement).
Module Int64Array3 := Array3Lib (StoreInt64AsElement).
Module UInt64Array3 := Array3Lib (StoreUInt64AsElement).
Module Int128Array3 := Array3Lib (StoreInt128AsElement).
Module UInt128Array3 := Array3Lib (StoreUInt128AsElement).
Module FloatArray3 := Array3Lib (StoreFloatAsElement).
Module DoubleArray3 := Array3Lib (StoreDoubleAsElement).
Module LongDoubleArray3 := Array3Lib (StoreLongDoubleAsElement).
Module FiniteFloatArray3 := Array3Lib (StoreFiniteFloatAsElement).
Module FiniteDoubleArray3 := Array3Lib (StoreFiniteDoubleAsElement).
Module FiniteLongDoubleArray3 := Array3Lib (StoreFiniteLongDoubleAsElement).
Module PtrArray3 := Array3Lib (StorePtrAsElement).

End Array3LibSig.
