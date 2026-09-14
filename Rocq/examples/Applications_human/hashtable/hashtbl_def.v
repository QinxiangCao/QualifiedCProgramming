Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Record Recordblist : Type := make_record_blist {
  blist_key : Z;
  blist_val : Z;
  blist_next : Z;
  blist_down : Z;
  blist_up : Z
}.

Definition zero_record_blist : Recordblist :=
  make_record_blist 0 0 0 0 0.

Definition StructPredblist (x : Z) (v : Recordblist) : Assertion :=
  ((&(x # "blist" ->ₛ "key")) # Ptr  |-> v.(blist_key)) **
  ((&(x # "blist" ->ₛ "val")) # UInt  |-> v.(blist_val)) **
  ((&(x # "blist" ->ₛ "next")) # Ptr  |-> v.(blist_next)) **
  ((&(x # "blist" ->ₛ "down")) # Ptr  |-> v.(blist_down)) **
  ((&(x # "blist" ->ₛ "up")) # Ptr  |-> v.(blist_up)).

Definition UndefStructPredblist (x : Z) : Assertion :=
  ((&(x # "blist" ->ₛ "key")) # Ptr  |->_) **
  ((&(x # "blist" ->ₛ "val")) # UInt  |->_) **
  ((&(x # "blist" ->ₛ "next")) # Ptr  |->_) **
  ((&(x # "blist" ->ₛ "down")) # Ptr  |->_) **
  ((&(x # "blist" ->ₛ "up")) # Ptr  |->_).

Lemma store_Predblist_to_undef : forall x v,
  StructPredblist x v |-- UndefStructPredblist x.
Proof.
  intros.
  unfold StructPredblist, UndefStructPredblist.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_uint_undef_store_uint.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ptr_undef_store_ptr.
  cancel.
Qed.

Lemma undefstore_Predblist_to_align : forall x,
  UndefStructPredblist x |-- store_align_n (((((0 + sizeof(PTR)) + sizeof(UINT)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)).
Proof.
  intros.
  unfold UndefStructPredblist.
  sep_apply undef_store_ptr_align.
  sep_apply undef_store_uint_align4.
  sep_apply undef_store_ptr_align.
  sep_apply undef_store_ptr_align.
  sep_apply undef_store_ptr_align.
  sep_apply store_align4_to_store_align.
  sep_apply (store_align_merge ptr_size_Z (4 * 1)).
  sep_apply (store_align_merge (ptr_size_Z + 4 * 1) ptr_size_Z).
  sep_apply (store_align_merge ((ptr_size_Z + 4 * 1) + ptr_size_Z) ptr_size_Z).
  sep_apply (store_align_merge (((ptr_size_Z + 4 * 1) + ptr_size_Z) + ptr_size_Z) ptr_size_Z).
  rewrite !sizeof_ptr.
  rewrite sizeof_uint.
  unfold ptr_size_Z.
  simpl.
  cancel.
Qed.

Lemma store_Predblist_to_align : forall x v,
  StructPredblist x v |-- store_align_n (((((0 + sizeof(PTR)) + sizeof(UINT)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)).
Proof.
  intros.
  sep_apply store_Predblist_to_undef.
  sep_apply undefstore_Predblist_to_align.
  cancel.
Qed.

Module StoreStructblistAsElement <: ELEMENT_STORE.
  Definition A := Recordblist.
  Definition sizeA := (((((0 + sizeof(PTR)) + sizeof(UINT)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)).
  Definition storeA (x: addr) (lo: Z) (a: Recordblist): Assertion :=
    (StructPredblist (x + lo * sizeA) a).
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (UndefStructPredblist (x + lo * sizeA)).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    unfold storeA, undefstoreA.
    sep_apply store_Predblist_to_undef.
    cancel.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA.
    replace (x + n * sizeA + lo * sizeA) with (x + (lo + n) * sizeA) by lia.
    reflexivity.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA.
    replace (x + n * sizeA + lo * sizeA) with (x + (lo + n) * sizeA) by lia.
    reflexivity.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    sep_apply store_Predblist_to_align.
    cancel.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    sep_apply undefstore_Predblist_to_align.
    cancel.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite !sizeof_ptr.
    rewrite sizeof_uint.
    unfold_arch.
    change Int.max_unsigned with 4294967295.
    lia.
  Qed.

End StoreStructblistAsElement.

Module StructblistArray := ArrayLib (StoreStructblistAsElement).
