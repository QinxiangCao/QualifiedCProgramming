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
From SimpleC.SL Require Import Mem CommonAssertion StoreAux.
Require Export ArrayLibCore.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type ArrayLibSig (CRules: SeparationLogicSig) (DePredSig : DerivedPredSig CRules) (SLibSig : StoreLibSig CRules DePredSig).

Include ArrayLibCoreSig CRules DePredSig SLibSig.

Import CRules.
Import DePredSig.
Import SLibSig.
Local Open Scope sac.

Module StoreCharAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(CHAR)) # Char |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(CHAR)) # Char |->_ .
  Definition sizeA := sizeof(CHAR).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_char_undef_store_char.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(CHAR) + lo * sizeof(CHAR)) with (x + (lo + n) * sizeof(CHAR)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(CHAR) + lo * sizeof(CHAR)) with (x + (lo + n) * sizeof(CHAR)) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_char.
    apply store_char_align.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_char.
    apply undef_store_char_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_char.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreCharAsElement.

Module CharArray := ArrayLib (StoreCharAsElement).

Module StoreUCharAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(UCHAR)) # UChar |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(UCHAR)) # UChar |->_ .
  Definition sizeA := sizeof(UCHAR).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_uchar_undef_store_uchar.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(UCHAR) + lo * sizeof(UCHAR)) with (x + (lo + n) * sizeof(UCHAR)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(UCHAR) + lo * sizeof(UCHAR)) with (x + (lo + n) * sizeof(UCHAR)) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_uchar.
    apply store_uchar_align.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_uchar.
    apply undef_store_uchar_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_uchar.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreUCharAsElement.

Module UCharArray := ArrayLib (StoreUCharAsElement).

Module StoreShortAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(SHORT)) # Short |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(SHORT)) # Short |->_ .
  Definition sizeA := sizeof(SHORT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_short_undef_store_short.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(SHORT) + lo * sizeof(SHORT)) with (x + (lo + n) * sizeof(SHORT)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(SHORT) + lo * sizeof(SHORT)) with (x + (lo + n) * sizeof(SHORT)) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_short.
    apply store_short_align.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_short.
    apply undef_store_short_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_short.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreShortAsElement.

Module ShortArray := ArrayLib (StoreShortAsElement).

Module StoreUShortAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(USHORT)) # UShort |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(USHORT)) # UShort |->_ .
  Definition sizeA := sizeof(USHORT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_ushort_undef_store_ushort.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(USHORT) + lo * sizeof(USHORT)) with (x + (lo + n) * sizeof(USHORT)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(USHORT) + lo * sizeof(USHORT)) with (x + (lo + n) * sizeof(USHORT)) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_ushort.
    apply store_ushort_align.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_ushort.
    apply undef_store_ushort_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_ushort.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreUShortAsElement.

Module UShortArray := ArrayLib (StoreUShortAsElement).

Module StoreIntAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(INT)) # Int |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(INT)) # Int |->_ .
  Definition sizeA := sizeof(INT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_int_undef_store_int.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(INT) + lo * sizeof(INT)) with (x + (lo + n) * sizeof(INT)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(INT) + lo * sizeof(INT)) with (x + (lo + n) * sizeof(INT)) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_int.
    eapply derivable1_trans.
    - apply store_int_align4.
    - replace 4 with (4 * 1) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_int.
    eapply derivable1_trans.
    - apply undef_store_int_align4.
    - replace 4 with (4 * 1) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_int.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreIntAsElement.

Module IntArray := ArrayLib (StoreIntAsElement).

Module StoreUIntAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(UINT)) # UInt |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(UINT)) # UInt |->_ .
  Definition sizeA := sizeof(UINT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_uint_undef_store_uint.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(UINT) + lo * sizeof(UINT)) with (x + (lo + n) * sizeof(UINT)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(UINT) + lo * sizeof(UINT)) with (x + (lo + n) * sizeof(UINT)) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_uint.
    eapply derivable1_trans.
    - apply store_uint_align4.
    - replace 4 with (4 * 1) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_uint.
    eapply derivable1_trans.
    - apply undef_store_uint_align4.
    - replace 4 with (4 * 1) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_uint.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreUIntAsElement.

Module UIntArray := ArrayLib (StoreUIntAsElement).

Module StoreInt64AsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(INT64)) # Int64 |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(INT64)) # Int64 |->_ .
  Definition sizeA := sizeof(INT64).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_int64_undef_store_int64.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(INT64) + lo * sizeof(INT64)) with (x + (lo + n) * sizeof(INT64)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(INT64) + lo * sizeof(INT64)) with (x + (lo + n) * sizeof(INT64)) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_int64.
    eapply derivable1_trans.
    - apply store_int64_align4.
    - replace 8 with (4 * 2) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_int64.
    eapply derivable1_trans.
    - apply undef_store_int64_align4.
    - replace 8 with (4 * 2) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_int64.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreInt64AsElement.

Module Int64Array := ArrayLib (StoreInt64AsElement).

Module StoreUInt64AsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(UINT64)) # UInt64 |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(UINT64)) # UInt64 |->_ .
  Definition sizeA := sizeof(UINT64).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_uint64_undef_store_uint64.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(UINT64) + lo * sizeof(UINT64)) with (x + (lo + n) * sizeof(UINT64)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(UINT64) + lo * sizeof(UINT64)) with (x + (lo + n) * sizeof(UINT64)) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_uint64.
    eapply derivable1_trans.
    - apply store_uint64_align4.
    - replace 8 with (4 * 2) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_uint64.
    eapply derivable1_trans.
    - apply undef_store_uint64_align4.
    - replace 8 with (4 * 2) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_uint64.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreUInt64AsElement.

Module UInt64Array := ArrayLib (StoreUInt64AsElement).

Module StorePtrAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * 4) # Ptr |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * 4) # Ptr |->_ .
  Definition sizeA := sizeof(PTR).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_ptr_undef_store_ptr.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_ptr.
    replace (x + n * 4 + lo * 4) with (x + (lo + n) * 4) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_ptr.
    replace (x + n * 4 + lo * 4) with (x + (lo + n) * 4) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    eapply derivable1_trans.
    - apply store_ptr_align4.
    - rewrite sizeof_ptr.
      replace 4 with (4 * 1) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    eapply derivable1_trans.
    - apply undef_store_ptr_align4.
    - rewrite sizeof_ptr.
      replace 4 with (4 * 1) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA. rewrite sizeof_ptr.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StorePtrAsElement.

Module PtrArray := ArrayLib (StorePtrAsElement).

Module StoreFloatAsElement <: ELEMENT_STORE.
  Definition A := fp32.
  Definition storeA (x: addr) (lo: Z) (a: fp32): Assertion :=
    (x + lo * sizeof(FLOAT)) # Float |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(FLOAT)) # Float |->_ .
  Definition sizeA := sizeof(FLOAT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_float_undef_store_float.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_float.
    replace (x + n * 4 + lo * 4) with (x + (lo + n) * 4) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_float.
    replace (x + n * 4 + lo * 4) with (x + (lo + n) * 4) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a,
    storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_float.
    apply store_float_align.
  Qed.

  Lemma undefstore_to_align : forall x lo,
    undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_float.
    eapply derivable1_trans.
    - apply undef_store_float_align4.
    - replace 4 with (4 * 1) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_float.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreFloatAsElement.

Module FloatArray := ArrayLib (StoreFloatAsElement).

Module StoreDoubleAsElement <: ELEMENT_STORE.
  Definition A := fp64.
  Definition storeA (x: addr) (lo: Z) (a: fp64): Assertion :=
    (x + lo * sizeof(DOUBLE)) # Double |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(DOUBLE)) # Double |->_ .
  Definition sizeA := sizeof(DOUBLE).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_double_undef_store_double.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_double.
    replace (x + n * 8 + lo * 8) with (x + (lo + n) * 8) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_double.
    replace (x + n * 8 + lo * 8) with (x + (lo + n) * 8) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a,
    storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_double.
    apply store_double_align.
  Qed.

  Lemma undefstore_to_align : forall x lo,
    undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_double.
    eapply derivable1_trans.
    - apply undef_store_double_align4.
    - replace 8 with (4 * 2) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_double.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreDoubleAsElement.

Module DoubleArray := ArrayLib (StoreDoubleAsElement).

Module StoreFiniteFloatAsElement <: ELEMENT_STORE.
  Definition A := fp32.
  Definition storeA (x: addr) (lo: Z) (a: fp32): Assertion :=
    (x + lo * sizeof(FLOAT)) # FiniteFloat |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(FLOAT)) # FiniteFloat |->_ .
  Definition sizeA := sizeof(FLOAT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_finite_float_undef_store_finite_float.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_float.
    replace (x + n * 4 + lo * 4) with (x + (lo + n) * 4) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_float.
    replace (x + n * 4 + lo * 4) with (x + (lo + n) * 4) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a,
    storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_float.
    apply store_finite_float_align.
  Qed.

  Lemma undefstore_to_align : forall x lo,
    undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA, undef_store_finite_float.
    rewrite sizeof_float.
    eapply derivable1_trans.
    - apply undef_store_float_align4.
    - replace 4 with (4 * 1) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_float.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreFiniteFloatAsElement.

Module FiniteFloatArray := ArrayLib (StoreFiniteFloatAsElement).

Module StoreFiniteDoubleAsElement <: ELEMENT_STORE.
  Definition A := fp64.
  Definition storeA (x: addr) (lo: Z) (a: fp64): Assertion :=
    (x + lo * sizeof(DOUBLE)) # FiniteDouble |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(DOUBLE)) # FiniteDouble |->_ .
  Definition sizeA := sizeof(DOUBLE).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_finite_double_undef_store_finite_double.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_double.
    replace (x + n * 8 + lo * 8) with (x + (lo + n) * 8) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    rewrite sizeof_double.
    replace (x + n * 8 + lo * 8) with (x + (lo + n) * 8) by lia.
    entailer!.
  Qed.

  Lemma store_to_align : forall x lo a,
    storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    rewrite sizeof_double.
    apply store_finite_double_align.
  Qed.

  Lemma undefstore_to_align : forall x lo,
    undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA, undef_store_finite_double.
    rewrite sizeof_double.
    eapply derivable1_trans.
    - apply undef_store_double_align4.
    - replace 8 with (4 * 2) by lia.
      apply store_align4_to_store_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_double.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreFiniteDoubleAsElement.

Module FiniteDoubleArray := ArrayLib (StoreFiniteDoubleAsElement).

End ArrayLibSig.
