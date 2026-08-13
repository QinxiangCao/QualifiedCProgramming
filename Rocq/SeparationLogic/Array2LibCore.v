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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type Array2LibCoreSig
  (Arch : CArchSig)
  (Endian : CEndianSig)
  (CRules: SeparationLogicSig)
  (DePredSig : DerivedPredSig Arch Endian CRules)
  (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
  (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig).

Import CRules.
Import DePredSig.
Import SLibSig.
Import ALibSig.
Local Open Scope sac.

Section GeneralArray2Rows.
  Variable (B : Type).
  Variable (storeB : addr -> Z -> B -> Assertion).
  Variable (undefB : addr -> Z -> Assertion).
  Hypothesis storeB_to_undefB : forall x lo b, storeB x lo b |-- undefB x lo.

  Lemma store_array_rec_to_undef_array_rec : forall x lo hi (l : list B),
    store_array_rec storeB x lo hi l |--
    store_undef_array_rec undefB x lo hi (Z.to_nat (hi - lo)).
  Proof.
    intros.
    prop_apply (store_array_rec_length B storeB x lo hi l).
    Intros.
    match goal with
    | Hlen : Z.of_nat (length l) = hi - lo |- _ =>
        revert x lo hi Hlen
    end.
    induction l; intros; simpl.
    - match goal with Hlen : _ |- _ => simpl in Hlen end.
      replace (Z.to_nat (hi - lo)) with 0%nat by lia.
      simpl.
      entailer!.
    - match goal with Hlen : _ |- _ => simpl in Hlen end.
      replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
      simpl.
      sep_apply storeB_to_undefB.
      sep_apply IHl; try lia.
      entailer!.
  Qed.

  Lemma store_array_to_undef_array : forall x n (l : list B),
    store_array storeB x n l |-- store_undef_array undefB x n.
  Proof.
    intros.
    unfold store_array, store_undef_array.
    sep_apply store_array_rec_to_undef_array_rec.
    replace (n - 0) with n by lia.
    entailer!.
  Qed.

  Lemma store_undef_array_rec_split_to_missing_i : forall x lo i hi,
    lo <= i < hi ->
    store_undef_array_rec undefB x lo hi (Z.to_nat (hi - lo)) |--
      undefB x i **
      store_undef_array_missing_i_rec undefB x i lo hi (Z.to_nat (hi - lo)).
  Proof.
    intros.
    revert H.
    set (len := Z.to_nat (hi - lo)).
    assert (len = Z.to_nat (hi - lo)) by lia.
    clearbody len.
    revert H.
    revert x lo i hi; induction len; intros; simpl.
    - entailer!.
    - pose proof Z_le_lt_eq_dec lo i ltac:(lia) as [? | ?].
      + Right.
        sep_apply (IHlen x (lo + 1) i hi); try lia.
        entailer!.
      + Left.
        subst i.
        entailer!.
  Qed.

  Lemma store_undef_array_split_to_missing_i : forall x i n,
    0 <= i < n ->
    store_undef_array undefB x n |--
      undefB x i **
      store_undef_array_missing_i_rec undefB x i 0 n (Z.to_nat n).
  Proof.
    intros.
    unfold store_undef_array.
    replace (Z.to_nat n) with (Z.to_nat (n - 0)) by lia.
    sep_apply (store_undef_array_rec_split_to_missing_i x 0 i n); try lia.
    entailer!.
  Qed.
End GeneralArray2Rows.

Module Array2Lib (ES: ELEMENT_STORE).

Import ES.
Module ElemArray := ArrayLib ES.

Definition row_addr (x : addr) (m i : Z) : addr :=
  x + i * m * sizeA.

Definition row_store (m : Z) (x : addr) (i : Z) (row : list A) : Assertion :=
  ElemArray.full (row_addr x m i) m row.

Definition mixed_row_store
  (m : Z) (x : addr) (i : Z) (row : list (option A)) : Assertion :=
  ElemArray.mixed_full (row_addr x m i) m row.

Definition undef_row_store (m : Z) (x : addr) (i : Z) : Assertion :=
  ElemArray.undef_full (row_addr x m i) m.

Definition full (x : addr) (n m : Z) (rows : list (list A)) : Assertion :=
  store_array (row_store m) x n rows.

Definition missing_i
  (x : addr) (i lo hi m : Z) (rows : list (list A)) : Assertion :=
  store_array_missing_i_rec (row_store m) x i lo hi rows.

Definition mixed_full
  (x : addr) (n m : Z) (rows : list (list (option A))) : Assertion :=
  store_array (mixed_row_store m) x n rows.

Definition mixed_missing_i
  (x : addr) (i lo hi m : Z) (rows : list (list (option A))) : Assertion :=
  store_array_missing_i_rec (mixed_row_store m) x i lo hi rows.

Definition undef_full (x : addr) (n m : Z) : Assertion :=
  store_undef_array (undef_row_store m) x n.

Definition undef_missing_i (x : addr) (i lo hi m : Z) : Assertion :=
  store_undef_array_missing_i_rec (undef_row_store m) x i lo hi (Z.to_nat (hi - lo)).

Lemma full_Zlength : forall x n m rows,
  full x n m rows |-- “ Zlength rows = n ”.
Proof.
  intros.
  unfold full.
  apply store_array_Zlength.
Qed.

Lemma mixed_full_Zlength : forall x n m rows,
  mixed_full x n m rows |-- “ Zlength rows = n ”.
Proof.
  intros.
  unfold mixed_full.
  apply store_array_Zlength.
Qed.

Lemma missing_i_Zlength : forall x i lo hi m rows,
  missing_i x i lo hi m rows |-- “ Zlength rows = hi - lo ”.
Proof.
  intros.
  unfold missing_i.
  apply store_array_missing_i_rec_Zlength.
Qed.

Lemma mixed_missing_i_Zlength : forall x i lo hi m rows,
  mixed_missing_i x i lo hi m rows |-- “ Zlength rows = hi - lo ”.
Proof.
  intros.
  unfold mixed_missing_i.
  apply store_array_missing_i_rec_Zlength.
Qed.

Lemma full_valid : forall x n m rows,
  full x n m rows |-- “ 0 <= n ”.
Proof.
  intros.
  unfold full.
  apply store_array_valid.
Qed.

Lemma mixed_full_valid : forall x n m rows,
  mixed_full x n m rows |-- “ 0 <= n ”.
Proof.
  intros.
  unfold mixed_full.
  apply store_array_valid.
Qed.

Lemma row_store_to_undef_row_store : forall x m i row,
  row_store m x i row |-- undef_row_store m x i.
Proof.
  intros.
  unfold row_store, undef_row_store.
  apply ElemArray.full_to_undef_full.
Qed.

Lemma mixed_row_store_to_undef_row_store : forall x m i row,
  mixed_row_store m x i row |-- undef_row_store m x i.
Proof.
  intros.
  unfold mixed_row_store, undef_row_store.
  apply ElemArray.mixed_full_to_undef_full.
Qed.

Lemma full_split_to_missing_i : forall x i n m rows,
  0 <= i < n ->
  full x n m rows |--
    ElemArray.full (row_addr x m i) m (Znth i rows nil) **
    missing_i x i 0 n m rows.
Proof.
  intros.
  unfold full, missing_i, row_store.
  eapply (store_array_split_to_missing_i (list A) (row_store m) x i n rows nil); eauto.
Qed.

Lemma missing_i_merge_to_full : forall x i n m rows row,
  0 <= i < n ->
  ElemArray.full (row_addr x m i) m row **
  missing_i x i 0 n m rows |--
    full x n m (replace_Znth i row rows).
Proof.
  intros.
  unfold full, missing_i, row_store.
  eapply (store_array_missing_i_merge_to_array (list A) (row_store m) x i n row rows); eauto.
Qed.

Lemma mixed_full_split_to_mixed_missing_i : forall x i n m rows,
  0 <= i < n ->
  mixed_full x n m rows |--
    ElemArray.mixed_full (row_addr x m i) m (Znth i rows nil) **
    mixed_missing_i x i 0 n m rows.
Proof.
  intros.
  unfold mixed_full, mixed_missing_i, mixed_row_store.
  eapply (store_array_split_to_missing_i (list (option A)) (mixed_row_store m) x i n rows nil); eauto.
Qed.

Lemma mixed_missing_i_merge_to_mixed_full : forall x i n m rows row,
  0 <= i < n ->
  ElemArray.mixed_full (row_addr x m i) m row **
  mixed_missing_i x i 0 n m rows |--
    mixed_full x n m (replace_Znth i row rows).
Proof.
  intros.
  unfold mixed_full, mixed_missing_i, mixed_row_store.
  eapply (store_array_missing_i_merge_to_array (list (option A)) (mixed_row_store m) x i n row rows); eauto.
Qed.

Lemma undef_full_split_to_undef_missing_i : forall x i n m,
  0 <= i < n ->
  undef_full x n m |--
  ElemArray.undef_full (row_addr x m i) m **
    undef_missing_i x i 0 n m.
Proof.
  intros.
  unfold undef_full, undef_missing_i.
  sep_apply (store_undef_array_split_to_missing_i (undef_row_store m) x i n); try lia.
  replace (Z.to_nat n) with (Z.to_nat (n - 0)) by lia.
  unfold undef_row_store.
  entailer!.
Qed.

Lemma full_to_undef_full : forall x n m rows,
  full x n m rows |-- undef_full x n m.
Proof.
  intros.
  unfold full, undef_full.
  eapply (store_array_to_undef_array (list A) (row_store m) (undef_row_store m)).
  intros.
  apply row_store_to_undef_row_store.
Qed.

Lemma mixed_full_to_undef_full : forall x n m rows,
  mixed_full x n m rows |-- undef_full x n m.
Proof.
  intros.
  unfold mixed_full, undef_full.
  eapply (store_array_to_undef_array (list (option A)) (mixed_row_store m) (undef_row_store m)).
  intros.
  apply mixed_row_store_to_undef_row_store.
Qed.

Lemma undef_full_valid : forall x n m,
  undef_full x n m |-- “ 0 <= n ”.
Proof.
  intros.
  unfold undef_full, store_undef_array.
  destruct (Z_le_gt_dec 0 n) as [Hn | Hn].
  - entailer!.
  - replace (Z.to_nat n) with 0%nat by lia.
    simpl.
    entailer!.
Qed.

End Array2Lib.

End Array2LibCoreSig.
