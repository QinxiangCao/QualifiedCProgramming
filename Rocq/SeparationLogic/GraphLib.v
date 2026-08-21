Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem CommonAssertion StoreAux ArrayLib Array2Lib PtrArray2Lib.
Require Export GraphLibCore.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Import ListNotations.
Local Open Scope list.

(**
  Public entry point for the graph memory library.

  [GraphLibCore.v] contains the generic templates.  This file exposes the
  concrete int-matrix instances currently used by DFS/Floyd.  Additional C cell
  types can be recovered by applying [MatrixRowsRepLib], [MatrixPtrRowsRepLib],
  or [MatrixLayoutStore] to the corresponding [ELEMENT_STORE].
*)

Module Type GraphLibSig
  (Arch : CArchSig)
  (Endian : CEndianSig)
  (CRules: SeparationLogicSig)
  (DePredSig : DerivedPredSig Arch Endian CRules)
  (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
  (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig)
  (A2LibSig : Array2LibSig Arch Endian CRules DePredSig SLibSig ALibSig)
  (P2LibSig : PtrArray2LibSig Arch Endian CRules DePredSig SLibSig ALibSig).

Include GraphLibCoreSig
  Arch Endian CRules DePredSig SLibSig ALibSig A2LibSig P2LibSig.

Import ALibSig.

Module IntMatrixLayoutStore := MatrixLayoutStore (StoreIntAsElement).
Module IntMatrixRowsRep := MatrixRowsRepLib (StoreIntAsElement).
Module IntPtrMatrixRowsRep := MatrixPtrRowsRepLib (StoreIntAsElement).

Module BooleanIntMatrixGraphModelLib (BG : BOOLEAN_MATRIX_GRAPH) :=
  BooleanMatrixGraphModelLib IntMatrixLayoutStore BG.

End GraphLibSig.
