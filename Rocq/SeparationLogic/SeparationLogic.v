Require Import Coq.ZArith.ZArith.
Require Import String.

From compcert.lib Require Export Integers.

From SimpleC.SL Require Export IntLib FloatLib ArrayLib Array2Lib Array3Lib PtrArray2Lib StoreAux MapLib StringLib.
From AUXLib Require Export ListLib.
From SimpleC.SL Require Export CommonAssertion.
From SimpleC.SL Require Assertion ConAssertion FunAssertion.

Module CRules32 <: SeparationLogicSig.
  Include Assertion.SL.
  Include DerivedPredSig Arch32 BigEndian.
  Include StoreLibSig Arch32 BigEndian.
  Include ArrayLibSig Arch32 BigEndian.
  Include Array2LibSig Arch32 BigEndian.
  Include Array3LibSig Arch32 BigEndian.
  Include PtrArray2LibSig Arch32 BigEndian.
  Include MapLibSig Arch32 BigEndian.
  Include StringLibSig Arch32 BigEndian.

End CRules32.

Module CRules := CRules32.

Module CRules64 <: SeparationLogicSig.
  Include Assertion.SL.
  Include DerivedPredSig Arch64 BigEndian.
  Include StoreLibSig Arch64 BigEndian.
  Include ArrayLibSig Arch64 BigEndian.
  Include Array2LibSig Arch64 BigEndian.
  Include Array3LibSig Arch64 BigEndian.
  Include PtrArray2LibSig Arch64 BigEndian.
  Include MapLibSig Arch64 BigEndian.
  Include StringLibSig Arch64 BigEndian.

End CRules64.

Module naiver_C_Rules32 <: ConAssertion.CSL ConAssertion.STS_naive <: SeparationLogicSig.
  Include ConAssertion.STS_naive.
  Include ConAssertion.CSL.
  Include DerivedPredSig Arch32 BigEndian.
  Include StoreLibSig Arch32 BigEndian.
  Include ArrayLibSig Arch32 BigEndian.
  Include Array2LibSig Arch32 BigEndian.
  Include Array3LibSig Arch32 BigEndian.
  Include PtrArray2LibSig Arch32 BigEndian.
  Include MapLibSig Arch32 BigEndian.
  Include StringLibSig Arch32 BigEndian.

End naiver_C_Rules32.

Module naiver_C_Rules64 <: ConAssertion.CSL ConAssertion.STS_naive <: SeparationLogicSig.
  Include ConAssertion.STS_naive.
  Include ConAssertion.CSL.
  Include DerivedPredSig Arch64 BigEndian.
  Include StoreLibSig Arch64 BigEndian.
  Include ArrayLibSig Arch64 BigEndian.
  Include Array2LibSig Arch64 BigEndian.
  Include Array3LibSig Arch64 BigEndian.
  Include PtrArray2LibSig Arch64 BigEndian.
  Include MapLibSig Arch64 BigEndian.
  Include StringLibSig Arch64 BigEndian.

End naiver_C_Rules64.

Module naive_C_Rules32 <: SeparationLogicSig.
  Include FunAssertion.SL.
  Include DerivedPredSig Arch32 BigEndian.
  Include StoreLibSig Arch32 BigEndian.
  Include ArrayLibSig Arch32 BigEndian.
  Include Array2LibSig Arch32 BigEndian.
  Include Array3LibSig Arch32 BigEndian.
  Include PtrArray2LibSig Arch32 BigEndian.
  Include MapLibSig Arch32 BigEndian.
  Include StringLibSig Arch32 BigEndian.

  Export SimpleCtypeNotations.
End naive_C_Rules32.

Module naive_C_Rules := naive_C_Rules32.

Module naive_C_Rules64 <: SeparationLogicSig.
  Include FunAssertion.SL.
  Include DerivedPredSig Arch64 BigEndian.
  Include StoreLibSig Arch64 BigEndian.
  Include ArrayLibSig Arch64 BigEndian.
  Include Array2LibSig Arch64 BigEndian.
  Include Array3LibSig Arch64 BigEndian.
  Include PtrArray2LibSig Arch64 BigEndian.
  Include MapLibSig Arch64 BigEndian.
  Include StringLibSig Arch64 BigEndian.

  Export SimpleCtypeNotations.
End naive_C_Rules64.

Module Snaive_C_Rules32 <: SeparationLogicSig.
  Include FunAssertion.SL.
  Include DerivedPredSig Arch32 BigEndian.
  Include StoreLibSig Arch32 BigEndian.
  Include ArrayLibSig Arch32 BigEndian.
  Include Array2LibSig Arch32 BigEndian.
  Include Array3LibSig Arch32 BigEndian.
  Include PtrArray2LibSig Arch32 BigEndian.
  Include MapLibSig Arch32 BigEndian.
  Include StringLibSig Arch32 BigEndian.

  Export SimpleCtypeNotations.
End Snaive_C_Rules32.

Module Snaive_C_Rules64 <: SeparationLogicSig.
  Include FunAssertion.SL.
  Include DerivedPredSig Arch64 BigEndian.
  Include StoreLibSig Arch64 BigEndian.
  Include ArrayLibSig Arch64 BigEndian.
  Include Array2LibSig Arch64 BigEndian.
  Include Array3LibSig Arch64 BigEndian.
  Include PtrArray2LibSig Arch64 BigEndian.
  Include MapLibSig Arch64 BigEndian.
  Include StringLibSig Arch64 BigEndian.

  Export SimpleCtypeNotations.
End Snaive_C_Rules64.

Parameter field_address : Z -> string -> string -> Z.
Definition should_be_equal {A : Type} (x y : A) : Prop := True.
