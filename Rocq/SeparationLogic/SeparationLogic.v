Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import String.
Require Import Permutation.

From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From compcert.lib Require Export Integers.

From SimpleC.SL Require Import Mem.
From SimpleC.SL Require Export IntLib FloatLib ArrayLib Array2Lib Array3Lib PtrArray2Lib StoreAux MapLib StringLib.
From AUXLib Require Export ListLib.
From SimpleC.SL Require Export CommonAssertion.
From SimpleC.SL Require Assertion ConAssertion CriticalSTS.

Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.

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
  Local Open Scope sac.

  Lemma ptr_size_eq_4 : ptr_size = 4%nat.
  Proof. solve_arch. Qed.

  Lemma ptr_size_Z_eq_4 : ptr_size_Z = 4.
  Proof. solve_arch. Qed.

  Lemma addr_max_unsigned_eq_int : addr_max_unsigned = Int.max_unsigned.
  Proof. solve_arch. Qed.

  Lemma undef_store_ptr_align4_32 : forall x,
    x # Ptr |->_ |-- store_align4_n 1.
  Proof.
    intros.
    apply undef_store_ptr_align4.
    apply ptr_size_eq_4.
  Qed.

  Lemma store_ptr_align4_32 : forall x v,
    x # Ptr |-> v |-- store_align4_n 1.
  Proof.
    intros.
    apply store_ptr_align4.
    apply ptr_size_eq_4.
  Qed.

  Lemma store_ptr_store_uint_32 : forall x v,
    x # Ptr |-> v |-- x # UInt |-> v.
  Proof.
    intros.
    apply store_ptr_store_uint.
    - apply ptr_size_eq_4.
    - apply addr_max_unsigned_eq_int.
  Qed.
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
  Local Open Scope sac.

  Lemma ptr_size_eq_8 : ptr_size = 8%nat.
  Proof. solve_arch. Qed.

  Lemma ptr_size_Z_eq_8 : ptr_size_Z = 8.
  Proof. solve_arch. Qed.

  Lemma addr_max_unsigned_eq_int64 : addr_max_unsigned = Int64.max_unsigned.
  Proof. solve_arch. Qed.

  Lemma undef_store_ptr_undef_store_uint64_64 : forall x,
    x # Ptr |->_ |-- x # UInt64 |->_.
  Proof.
    intros.
    apply undef_store_ptr_undef_store_uint64.
    apply ptr_size_eq_8.
  Qed.

  Lemma undef_store_ptr_align4_64 : forall x,
    x # Ptr |->_ |-- store_align4_n 2.
  Proof.
    intros.
    eapply derivable1_trans.
    - apply undef_store_ptr_undef_store_uint64_64.
    - apply undef_store_uint64_align4.
  Qed.

  Lemma store_ptr_align4_64 : forall x v,
    x # Ptr |-> v |-- store_align4_n 2.
  Proof.
    intros.
    sep_apply store_ptr_undef_store_ptr.
    sep_apply undef_store_ptr_align4_64.
    entailer!.
  Qed.

  Lemma store_ptr_store_uint64_64 : forall x v,
    x # Ptr |-> v |-- x # UInt64 |-> v.
  Proof.
    intros.
    apply store_ptr_store_uint64.
    - apply ptr_size_eq_8.
    - apply addr_max_unsigned_eq_int64.
  Qed.
End CRules64.

Module naive_C_Rules32 <: ConAssertion.CSL ConAssertion.STS_naive <: SeparationLogicSig.
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
  Local Open Scope sac.

  Lemma ptr_size_eq_4 : ptr_size = 4%nat.
  Proof. solve_arch. Qed.

  Lemma ptr_size_Z_eq_4 : ptr_size_Z = 4.
  Proof. solve_arch. Qed.

  Lemma addr_max_unsigned_eq_int : addr_max_unsigned = Int.max_unsigned.
  Proof. solve_arch. Qed.

  Lemma undef_store_ptr_align4_32 : forall x,
    x # Ptr |->_ |-- store_align4_n 1.
  Proof.
    intros.
    apply undef_store_ptr_align4.
    apply ptr_size_eq_4.
  Qed.

  Lemma store_ptr_align4_32 : forall x v,
    x # Ptr |-> v |-- store_align4_n 1.
  Proof.
    intros.
    apply store_ptr_align4.
    apply ptr_size_eq_4.
  Qed.

  Lemma store_ptr_store_uint_32 : forall x v,
    x # Ptr |-> v |-- x # UInt |-> v.
  Proof.
    intros.
    apply store_ptr_store_uint.
    - apply ptr_size_eq_4.
    - apply addr_max_unsigned_eq_int.
  Qed.
End naive_C_Rules32.

Module naive_C_Rules := naive_C_Rules32.

Module naive_C_Rules64 <: ConAssertion.CSL ConAssertion.STS_naive <: SeparationLogicSig.
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
  Local Open Scope sac.

  Lemma ptr_size_eq_8 : ptr_size = 8%nat.
  Proof. solve_arch. Qed.

  Lemma ptr_size_Z_eq_8 : ptr_size_Z = 8.
  Proof. solve_arch. Qed.

  Lemma addr_max_unsigned_eq_int64 : addr_max_unsigned = Int64.max_unsigned.
  Proof. solve_arch. Qed.

  Lemma undef_store_ptr_undef_store_uint64_64 : forall x,
    x # Ptr |->_ |-- x # UInt64 |->_.
  Proof.
    intros.
    apply undef_store_ptr_undef_store_uint64.
    apply ptr_size_eq_8.
  Qed.

  Lemma undef_store_ptr_align4_64 : forall x,
    x # Ptr |->_ |-- store_align4_n 2.
  Proof.
    intros.
    eapply derivable1_trans.
    - apply undef_store_ptr_undef_store_uint64_64.
    - apply undef_store_uint64_align4.
  Qed.

  Lemma store_ptr_align4_64 : forall x v,
    x # Ptr |-> v |-- store_align4_n 2.
  Proof.
    intros.
    sep_apply store_ptr_undef_store_ptr.
    sep_apply undef_store_ptr_align4_64.
    entailer!.
  Qed.

  Lemma store_ptr_store_uint64_64 : forall x v,
    x # Ptr |-> v |-- x # UInt64 |-> v.
  Proof.
    intros.
    apply store_ptr_store_uint64.
    - apply ptr_size_eq_8.
    - apply addr_max_unsigned_eq_int64.
  Qed.
End naive_C_Rules64.

Module Snaive_C_Rules32 <: ConAssertion.CSL ConAssertion.STS_naive <: SeparationLogicSig.
  Include ConAssertion.STS_naive.
  Include ConAssertion.CSL.
  Include DerivedPredSig Arch32 LittleEndian.
  Include StoreLibSig Arch32 LittleEndian.
  Include ArrayLibSig Arch32 LittleEndian.
  Include Array2LibSig Arch32 LittleEndian.
  Include Array3LibSig Arch32 LittleEndian.
  Include PtrArray2LibSig Arch32 LittleEndian.
  Include MapLibSig Arch32 LittleEndian.
  Include StringLibSig Arch32 LittleEndian.
  Local Open Scope sac.

  Lemma ptr_size_eq_4 : ptr_size = 4%nat.
  Proof. solve_arch. Qed.

  Lemma ptr_size_Z_eq_4 : ptr_size_Z = 4.
  Proof. solve_arch. Qed.

  Lemma addr_max_unsigned_eq_int : addr_max_unsigned = Int.max_unsigned.
  Proof. solve_arch. Qed.

  Lemma undef_store_ptr_align4_32 : forall x,
    x # Ptr |->_ |-- store_align4_n 1.
  Proof.
    intros.
    apply undef_store_ptr_align4.
    apply ptr_size_eq_4.
  Qed.

  Lemma store_ptr_align4_32 : forall x v,
    x # Ptr |-> v |-- store_align4_n 1.
  Proof.
    intros.
    apply store_ptr_align4.
    apply ptr_size_eq_4.
  Qed.

  Lemma store_ptr_store_uint_32 : forall x v,
    x # Ptr |-> v |-- x # UInt |-> v.
  Proof.
    intros.
    apply store_ptr_store_uint.
    - apply ptr_size_eq_4.
    - apply addr_max_unsigned_eq_int.
  Qed.
End Snaive_C_Rules32.

Module Snaive_C_Rules := Snaive_C_Rules32.

Module Snaive_C_Rules64 <: ConAssertion.CSL ConAssertion.STS_naive <: SeparationLogicSig.
  Include ConAssertion.STS_naive.
  Include ConAssertion.CSL.
  Include DerivedPredSig Arch64 LittleEndian.
  Include StoreLibSig Arch64 LittleEndian.
  Include ArrayLibSig Arch64 LittleEndian.
  Include Array2LibSig Arch64 LittleEndian.
  Include Array3LibSig Arch64 LittleEndian.
  Include PtrArray2LibSig Arch64 LittleEndian.
  Include MapLibSig Arch64 LittleEndian.
  Include StringLibSig Arch64 LittleEndian.
  Local Open Scope sac.

  Lemma ptr_size_eq_8 : ptr_size = 8%nat.
  Proof. solve_arch. Qed.

  Lemma ptr_size_Z_eq_8 : ptr_size_Z = 8.
  Proof. solve_arch. Qed.

  Lemma addr_max_unsigned_eq_int64 : addr_max_unsigned = Int64.max_unsigned.
  Proof. solve_arch. Qed.

  Lemma undef_store_ptr_undef_store_uint64_64 : forall x,
    x # Ptr |->_ |-- x # UInt64 |->_.
  Proof.
    intros.
    apply undef_store_ptr_undef_store_uint64.
    apply ptr_size_eq_8.
  Qed.

  Lemma undef_store_ptr_align4_64 : forall x,
    x # Ptr |->_ |-- store_align4_n 2.
  Proof.
    intros.
    eapply derivable1_trans.
    - apply undef_store_ptr_undef_store_uint64_64.
    - apply undef_store_uint64_align4.
  Qed.

  Lemma store_ptr_align4_64 : forall x v,
    x # Ptr |-> v |-- store_align4_n 2.
  Proof.
    intros.
    sep_apply store_ptr_undef_store_ptr.
    sep_apply undef_store_ptr_align4_64.
    entailer!.
  Qed.

  Lemma store_ptr_store_uint64_64 : forall x v,
    x # Ptr |-> v |-- x # UInt64 |-> v.
  Proof.
    intros.
    apply store_ptr_store_uint64.
    - apply ptr_size_eq_8.
    - apply addr_max_unsigned_eq_int64.
  Qed.
End Snaive_C_Rules64.

Parameter field_address : Z -> string -> string -> Z.
Definition should_be_equal {A : Type} (x y : A) : Prop := True.
