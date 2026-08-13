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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type Array3LibCoreSig
  (Arch : CArchSig)
  (Endian : CEndianSig)
  (CRules: SeparationLogicSig)
  (DePredSig : DerivedPredSig Arch Endian CRules)
  (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
  (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig)
  (A2LibSig : Array2LibSig Arch Endian CRules DePredSig SLibSig ALibSig).

Import CRules.
Import DePredSig.
Import SLibSig.
Import ALibSig.
Import A2LibSig.
Local Open Scope sac.

Module Array3Lib (ES: ELEMENT_STORE).

Import ES.
Module PlaneArray := Array2Lib ES.

Definition plane_addr (x : addr) (m k i : Z) : addr :=
  x + i * m * k * sizeA.

Definition plane_store
  (m k : Z) (x : addr) (i : Z) (plane : list (list A)) : Assertion :=
  PlaneArray.full (plane_addr x m k i) m k plane.

Definition mixed_plane_store
  (m k : Z) (x : addr) (i : Z) (plane : list (list (option A))) : Assertion :=
  PlaneArray.mixed_full (plane_addr x m k i) m k plane.

Definition undef_plane_store (m k : Z) (x : addr) (i : Z) : Assertion :=
  PlaneArray.undef_full (plane_addr x m k i) m k.

Definition full
  (x : addr) (n m k : Z) (planes : list (list (list A))) : Assertion :=
  store_array (plane_store m k) x n planes.

Definition missing_i
  (x : addr) (i lo hi m k : Z) (planes : list (list (list A))) : Assertion :=
  store_array_missing_i_rec (plane_store m k) x i lo hi planes.

Definition mixed_full
  (x : addr) (n m k : Z) (planes : list (list (list (option A)))) : Assertion :=
  store_array (mixed_plane_store m k) x n planes.

Definition mixed_missing_i
  (x : addr) (i lo hi m k : Z) (planes : list (list (list (option A)))) : Assertion :=
  store_array_missing_i_rec (mixed_plane_store m k) x i lo hi planes.

Definition undef_full (x : addr) (n m k : Z) : Assertion :=
  store_undef_array (undef_plane_store m k) x n.

Definition undef_missing_i (x : addr) (i lo hi m k : Z) : Assertion :=
  store_undef_array_missing_i_rec
    (undef_plane_store m k) x i lo hi (Z.to_nat (hi - lo)).

Lemma full_Zlength : forall x n m k planes,
  full x n m k planes |-- “ Zlength planes = n ”.
Proof.
  intros.
  unfold full.
  apply store_array_Zlength.
Qed.

Lemma mixed_full_Zlength : forall x n m k planes,
  mixed_full x n m k planes |-- “ Zlength planes = n ”.
Proof.
  intros.
  unfold mixed_full.
  apply store_array_Zlength.
Qed.

Lemma missing_i_Zlength : forall x i lo hi m k planes,
  missing_i x i lo hi m k planes |-- “ Zlength planes = hi - lo ”.
Proof.
  intros.
  unfold missing_i.
  apply store_array_missing_i_rec_Zlength.
Qed.

Lemma mixed_missing_i_Zlength : forall x i lo hi m k planes,
  mixed_missing_i x i lo hi m k planes |-- “ Zlength planes = hi - lo ”.
Proof.
  intros.
  unfold mixed_missing_i.
  apply store_array_missing_i_rec_Zlength.
Qed.

Lemma full_valid : forall x n m k planes,
  full x n m k planes |-- “ 0 <= n ”.
Proof.
  intros.
  unfold full.
  apply store_array_valid.
Qed.

Lemma mixed_full_valid : forall x n m k planes,
  mixed_full x n m k planes |-- “ 0 <= n ”.
Proof.
  intros.
  unfold mixed_full.
  apply store_array_valid.
Qed.

Lemma plane_store_to_undef_plane_store : forall x m k i plane,
  plane_store m k x i plane |-- undef_plane_store m k x i.
Proof.
  intros.
  unfold plane_store, undef_plane_store.
  apply PlaneArray.full_to_undef_full.
Qed.

Lemma mixed_plane_store_to_undef_plane_store : forall x m k i plane,
  mixed_plane_store m k x i plane |-- undef_plane_store m k x i.
Proof.
  intros.
  unfold mixed_plane_store, undef_plane_store.
  apply PlaneArray.mixed_full_to_undef_full.
Qed.

Lemma full_split_to_missing_i : forall x i n m k planes,
  0 <= i < n ->
  full x n m k planes |--
    PlaneArray.full (plane_addr x m k i) m k (Znth i planes nil) **
    missing_i x i 0 n m k planes.
Proof.
  intros.
  unfold full, missing_i, plane_store.
  eapply (store_array_split_to_missing_i
    (list (list A)) (plane_store m k) x i n planes nil); eauto.
Qed.

Lemma missing_i_merge_to_full : forall x i n m k planes plane,
  0 <= i < n ->
  PlaneArray.full (plane_addr x m k i) m k plane **
  missing_i x i 0 n m k planes |--
    full x n m k (replace_Znth i plane planes).
Proof.
  intros.
  unfold full, missing_i, plane_store.
  eapply (store_array_missing_i_merge_to_array
    (list (list A)) (plane_store m k) x i n plane planes); eauto.
Qed.

Lemma mixed_full_split_to_mixed_missing_i : forall x i n m k planes,
  0 <= i < n ->
  mixed_full x n m k planes |--
    PlaneArray.mixed_full (plane_addr x m k i) m k (Znth i planes nil) **
    mixed_missing_i x i 0 n m k planes.
Proof.
  intros.
  unfold mixed_full, mixed_missing_i, mixed_plane_store.
  eapply (store_array_split_to_missing_i
    (list (list (option A))) (mixed_plane_store m k) x i n planes nil); eauto.
Qed.

Lemma mixed_missing_i_merge_to_mixed_full : forall x i n m k planes plane,
  0 <= i < n ->
  PlaneArray.mixed_full (plane_addr x m k i) m k plane **
  mixed_missing_i x i 0 n m k planes |--
    mixed_full x n m k (replace_Znth i plane planes).
Proof.
  intros.
  unfold mixed_full, mixed_missing_i, mixed_plane_store.
  eapply (store_array_missing_i_merge_to_array
    (list (list (option A))) (mixed_plane_store m k) x i n plane planes); eauto.
Qed.

Lemma undef_full_split_to_undef_missing_i : forall x i n m k,
  0 <= i < n ->
  undef_full x n m k |--
    PlaneArray.undef_full (plane_addr x m k i) m k **
    undef_missing_i x i 0 n m k.
Proof.
  intros.
  unfold undef_full, undef_missing_i.
  sep_apply (store_undef_array_split_to_missing_i (undef_plane_store m k) x i n); try lia.
  replace (Z.to_nat n) with (Z.to_nat (n - 0)) by lia.
  unfold undef_plane_store.
  entailer!.
Qed.

Lemma full_to_undef_full : forall x n m k planes,
  full x n m k planes |-- undef_full x n m k.
Proof.
  intros.
  unfold full, undef_full.
  eapply (store_array_to_undef_array
    (list (list A)) (plane_store m k) (undef_plane_store m k)).
  intros.
  apply plane_store_to_undef_plane_store.
Qed.

Lemma mixed_full_to_undef_full : forall x n m k planes,
  mixed_full x n m k planes |-- undef_full x n m k.
Proof.
  intros.
  unfold mixed_full, undef_full.
  eapply (store_array_to_undef_array
    (list (list (option A))) (mixed_plane_store m k) (undef_plane_store m k)).
  intros.
  apply mixed_plane_store_to_undef_plane_store.
Qed.

Lemma undef_full_valid : forall x n m k,
  undef_full x n m k |-- “ 0 <= n ”.
Proof.
  intros.
  unfold undef_full, store_undef_array.
  destruct (Z_le_gt_dec 0 n) as [Hn | Hn].
  - entailer!.
  - replace (Z.to_nat n) with 0%nat by lia.
    simpl.
    entailer!.
Qed.

End Array3Lib.

End Array3LibCoreSig.
