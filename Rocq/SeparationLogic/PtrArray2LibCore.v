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

Module Type PtrArray2LibCoreSig
  (ArchImpl : CArchSig)
  (Endian : CEndianSig)
  (CRules: SeparationLogicSig)
  (DePredSig : DerivedPredSig ArchImpl Endian CRules)
  (SLibSig : StoreLibSig ArchImpl Endian CRules DePredSig)
  (ALibSig : ArrayLibSig ArchImpl Endian CRules DePredSig SLibSig).

Import CRules.
Import DePredSig.
Import SLibSig.
Import ALibSig.
Local Open Scope sac.

Module PtrArray2Lib (ES: ELEMENT_STORE).

Import ES.
Module ElemArray := ArrayLib ES.

Definition row_block (pr : addr * list A) : Assertion :=
  ElemArray.full (fst pr) (Zlength (snd pr)) (snd pr).

Definition mixed_row_block
  (pr : addr * list (option A)) : Assertion :=
  ElemArray.mixed_full (fst pr) (Zlength (snd pr)) (snd pr).

Definition row_blocks (row_ptrs : list Z) (rows : list (list A)) : Assertion :=
  iter_sepcon (map row_block (combine row_ptrs rows)).

Definition mixed_row_blocks
  (row_ptrs : list Z) (rows : list (list (option A))) : Assertion :=
  iter_sepcon (map mixed_row_block (combine row_ptrs rows)).

Definition row_blocks_missing_i
  (i : Z) (row_ptrs : list Z) (rows : list (list A)) : Assertion :=
  iter_sepcon (map row_block (remove_Znth i (combine row_ptrs rows))).

Definition mixed_row_blocks_missing_i
  (i : Z) (row_ptrs : list Z) (rows : list (list (option A))) : Assertion :=
  iter_sepcon (map mixed_row_block (remove_Znth i (combine row_ptrs rows))).

Definition full (x : addr) (n : Z) (rows : list (list A)) : Assertion :=
  EX row_ptrs : list Z,
    “ Zlength row_ptrs = n /\ Zlength rows = n ” &&
    PtrArray.full x n row_ptrs **
    row_blocks row_ptrs rows.

Definition missing_i
  (x : addr) (n i row_ptr : Z) (rows : list (list A)) : Assertion :=
  EX row_ptrs : list Z,
    “ Zlength row_ptrs = n /\ Zlength rows = n /\ row_ptr = Znth i row_ptrs 0 ” &&
    PtrArray.missing_i x i 0 n row_ptrs **
    row_blocks_missing_i i row_ptrs rows.

Definition mixed_full
  (x : addr) (n : Z) (rows : list (list (option A))) : Assertion :=
  EX row_ptrs : list Z,
    “ Zlength row_ptrs = n /\ Zlength rows = n ” &&
    PtrArray.full x n row_ptrs **
    mixed_row_blocks row_ptrs rows.

Definition mixed_missing_i
  (x : addr) (n i row_ptr : Z) (rows : list (list (option A))) : Assertion :=
  EX row_ptrs : list Z,
    “ Zlength row_ptrs = n /\ Zlength rows = n /\ row_ptr = Znth i row_ptrs 0 ” &&
    PtrArray.missing_i x i 0 n row_ptrs **
    mixed_row_blocks_missing_i i row_ptrs rows.

Definition undef_full (x : addr) (n : Z) : Assertion :=
  PtrArray.undef_full x n.

Lemma full_Zlength : forall x n rows,
  full x n rows |-- “ Zlength rows = n ”.
Proof.
  intros.
  unfold full.
  Intros row_ptrs.
  entailer!.
Qed.

Lemma mixed_full_Zlength : forall x n rows,
  mixed_full x n rows |-- “ Zlength rows = n ”.
Proof.
  intros.
  unfold mixed_full.
  Intros row_ptrs.
  entailer!.
Qed.

Lemma undef_full_valid : forall x n,
  undef_full x n |-- “ 0 <= n ”.
Proof.
  intros.
  unfold undef_full.
  apply PtrArray.undef_full_valid.
Qed.

Lemma row_blocks_split_to_missing_i : forall i row_ptrs rows,
  0 <= i < Zlength row_ptrs ->
  Zlength row_ptrs = Zlength rows ->
  row_blocks row_ptrs rows |--
    ElemArray.full
      (Znth i row_ptrs 0)
      (Zlength (Znth i rows nil))
      (Znth i rows nil) **
    row_blocks_missing_i i row_ptrs rows.
Proof.
  intros.
  unfold row_blocks, row_blocks_missing_i, row_block.
  assert (Hcombine : 0 <= i < Zlength (combine row_ptrs rows)).
  { rewrite Zlength_combine. lia. }
  assert (Hmap : 0 <= i < Zlength (map row_block (combine row_ptrs rows))).
  { rewrite Zlength_map. exact Hcombine. }
  sep_apply (iter_sepcon_split_remove_Znth
    i (map row_block (combine row_ptrs rows)) (row_block (0, nil)) Hmap).
  rewrite (Znth_map row_block (combine row_ptrs rows) i (0, nil) (row_block (0, nil)))
    by exact Hcombine.
  rewrite <- map_remove_Znth.
  assert (HZnth:
    Znth i (combine row_ptrs rows) (0, nil) =
    (Znth i row_ptrs 0, Znth i rows nil)).
  { apply Znth_combine; lia. }
  assert (Hrow:
    row_block (Znth i (combine row_ptrs rows) (0, nil)) |--
    ElemArray.full (Znth i row_ptrs 0)
      (Zlength (Znth i rows nil)) (Znth i rows nil)).
  { rewrite HZnth. unfold row_block. simpl. entailer!. }
  sep_apply Hrow.
  entailer!.
Qed.

Lemma mixed_row_blocks_split_to_missing_i : forall i row_ptrs rows,
  0 <= i < Zlength row_ptrs ->
  Zlength row_ptrs = Zlength rows ->
  mixed_row_blocks row_ptrs rows |--
    ElemArray.mixed_full
      (Znth i row_ptrs 0)
      (Zlength (Znth i rows nil))
      (Znth i rows nil) **
    mixed_row_blocks_missing_i i row_ptrs rows.
Proof.
  intros.
  unfold mixed_row_blocks, mixed_row_blocks_missing_i, mixed_row_block.
  assert (Hcombine : 0 <= i < Zlength (combine row_ptrs rows)).
  { rewrite Zlength_combine. lia. }
  assert (Hmap : 0 <= i < Zlength (map mixed_row_block (combine row_ptrs rows))).
  { rewrite Zlength_map. exact Hcombine. }
  sep_apply (iter_sepcon_split_remove_Znth
    i (map mixed_row_block (combine row_ptrs rows)) (mixed_row_block (0, nil)) Hmap).
  rewrite (Znth_map mixed_row_block (combine row_ptrs rows) i (0, nil) (mixed_row_block (0, nil)))
    by exact Hcombine.
  rewrite <- map_remove_Znth.
  assert (HZnth:
    Znth i (combine row_ptrs rows) (0, nil) =
    (Znth i row_ptrs 0, Znth i rows nil)).
  { apply Znth_combine; lia. }
  assert (Hrow:
    mixed_row_block (Znth i (combine row_ptrs rows) (0, nil)) |--
    ElemArray.mixed_full (Znth i row_ptrs 0)
      (Zlength (Znth i rows nil)) (Znth i rows nil)).
  { rewrite HZnth. unfold mixed_row_block. simpl. entailer!. }
  sep_apply Hrow.
  entailer!.
Qed.

Lemma row_blocks_missing_i_merge_to_full : forall i row_ptrs rows row,
  0 <= i < Zlength row_ptrs ->
  Zlength row_ptrs = Zlength rows ->
  ElemArray.full (Znth i row_ptrs 0) (Zlength row) row **
  row_blocks_missing_i i row_ptrs rows |--
    row_blocks row_ptrs (replace_Znth i row rows).
Proof.
  intros.
  unfold row_blocks, row_blocks_missing_i, row_block.
  assert (Hcombine : 0 <= i < Zlength (combine row_ptrs rows)).
  { rewrite Zlength_combine. lia. }
  assert (Hmap : 0 <= i < Zlength (map row_block (combine row_ptrs rows))).
  { rewrite Zlength_map. exact Hcombine. }
  replace (combine row_ptrs (replace_Znth i row rows))
    with (replace_Znth i (Znth i row_ptrs 0, row) (combine row_ptrs rows)).
  2: { apply replace_Znth_combine_r. }
  rewrite map_replace_Znth.
  rewrite map_remove_Znth.
  sep_apply (iter_sepcon_merge_remove_Znth
    i (map row_block (combine row_ptrs rows))
    (row_block (Znth i row_ptrs 0, row)) Hmap).
  simpl.
  entailer!.
Qed.

Lemma mixed_row_blocks_missing_i_merge_to_full : forall i row_ptrs rows row,
  0 <= i < Zlength row_ptrs ->
  Zlength row_ptrs = Zlength rows ->
  ElemArray.mixed_full (Znth i row_ptrs 0) (Zlength row) row **
  mixed_row_blocks_missing_i i row_ptrs rows |--
    mixed_row_blocks row_ptrs (replace_Znth i row rows).
Proof.
  intros.
  unfold mixed_row_blocks, mixed_row_blocks_missing_i, mixed_row_block.
  assert (Hcombine : 0 <= i < Zlength (combine row_ptrs rows)).
  { rewrite Zlength_combine. lia. }
  assert (Hmap : 0 <= i < Zlength (map mixed_row_block (combine row_ptrs rows))).
  { rewrite Zlength_map. exact Hcombine. }
  replace (combine row_ptrs (replace_Znth i row rows))
    with (replace_Znth i (Znth i row_ptrs 0, row) (combine row_ptrs rows)).
  2: { apply replace_Znth_combine_r. }
  rewrite map_replace_Znth.
  rewrite map_remove_Znth.
  sep_apply (iter_sepcon_merge_remove_Znth
    i (map mixed_row_block (combine row_ptrs rows))
    (mixed_row_block (Znth i row_ptrs 0, row)) Hmap).
  simpl.
  entailer!.
Qed.

Lemma full_split_to_missing_i : forall x i n rows,
  0 <= i < n ->
  full x n rows |--
    EX row_ptr,
      StorePtrAsElement.storeA x i row_ptr **
      ElemArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil) **
      missing_i x n i row_ptr rows.
Proof.
  intros.
  unfold full, missing_i.
  Intros row_ptrs.
  destruct H0 as [Hrow_ptrs Hrows].
  Exists (Znth i row_ptrs 0).
  Exists row_ptrs.
  entailer!.
  assert (Hi_ptrs : 0 <= i < Zlength row_ptrs) by lia.
  assert (Hlen_rows : Zlength row_ptrs = Zlength rows) by lia.
  sep_apply (PtrArray.full_split_to_missing_i x i n row_ptrs 0 H).
  sep_apply (row_blocks_split_to_missing_i i row_ptrs rows Hi_ptrs Hlen_rows).
  entailer!.
Qed.

Lemma missing_i_merge_to_full : forall x i n row_ptr rows row,
  0 <= i < n ->
  StorePtrAsElement.storeA x i row_ptr **
  ElemArray.full row_ptr (Zlength row) row **
  missing_i x n i row_ptr rows |--
    full x n (replace_Znth i row rows).
Proof.
  intros.
  unfold missing_i, full.
  Intros row_ptrs.
  destruct H0 as [Hrow_ptrs [Hrows Hrow_ptr]].
  subst row_ptr.
  Exists row_ptrs.
  entailer!.
  - assert (Hi_ptrs : 0 <= i < Zlength row_ptrs) by lia.
    assert (Hlen_rows : Zlength row_ptrs = Zlength rows) by lia.
    eapply derivable1_trans with
      (y := (StorePtrAsElement.storeA x i (Znth i row_ptrs 0) **
             PtrArray.missing_i x i 0 n row_ptrs) **
            (ElemArray.full (Znth i row_ptrs 0) (Zlength row) row **
             row_blocks_missing_i i row_ptrs rows)).
    + entailer!.
    + unfold StorePtrAsElement.storeA at 1.
      sep_apply (PtrArray.missing_i_merge_to_full
        x i n (Znth i row_ptrs 0) row_ptrs H).
      rewrite replace_Znth_Znth by auto.
      sep_apply (row_blocks_missing_i_merge_to_full
        i row_ptrs rows row Hi_ptrs Hlen_rows).
      entailer!.
  - rewrite Zlength_replace_Znth.
    auto.
Qed.

Lemma mixed_full_split_to_mixed_missing_i : forall x i n rows,
  0 <= i < n ->
  mixed_full x n rows |--
    EX row_ptr,
      StorePtrAsElement.storeA x i row_ptr **
      ElemArray.mixed_full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil) **
      mixed_missing_i x n i row_ptr rows.
Proof.
  intros.
  unfold mixed_full, mixed_missing_i.
  Intros row_ptrs.
  destruct H0 as [Hrow_ptrs Hrows].
  Exists (Znth i row_ptrs 0).
  Exists row_ptrs.
  entailer!.
  assert (Hi_ptrs : 0 <= i < Zlength row_ptrs) by lia.
  assert (Hlen_rows : Zlength row_ptrs = Zlength rows) by lia.
  sep_apply (PtrArray.full_split_to_missing_i x i n row_ptrs 0 H).
  sep_apply (mixed_row_blocks_split_to_missing_i i row_ptrs rows Hi_ptrs Hlen_rows).
  entailer!.
Qed.

Lemma mixed_missing_i_merge_to_mixed_full : forall x i n row_ptr rows row,
  0 <= i < n ->
  StorePtrAsElement.storeA x i row_ptr **
  ElemArray.mixed_full row_ptr (Zlength row) row **
  mixed_missing_i x n i row_ptr rows |--
    mixed_full x n (replace_Znth i row rows).
Proof.
  intros.
  unfold mixed_missing_i, mixed_full.
  Intros row_ptrs.
  destruct H0 as [Hrow_ptrs [Hrows Hrow_ptr]].
  subst row_ptr.
  Exists row_ptrs.
  entailer!.
  - assert (Hi_ptrs : 0 <= i < Zlength row_ptrs) by lia.
    assert (Hlen_rows : Zlength row_ptrs = Zlength rows) by lia.
    eapply derivable1_trans with
      (y := (StorePtrAsElement.storeA x i (Znth i row_ptrs 0) **
             PtrArray.missing_i x i 0 n row_ptrs) **
            (ElemArray.mixed_full (Znth i row_ptrs 0) (Zlength row) row **
             mixed_row_blocks_missing_i i row_ptrs rows)).
    + entailer!.
    + unfold StorePtrAsElement.storeA at 1.
      sep_apply (PtrArray.missing_i_merge_to_full
        x i n (Znth i row_ptrs 0) row_ptrs H).
      rewrite replace_Znth_Znth by auto.
      sep_apply (mixed_row_blocks_missing_i_merge_to_full
        i row_ptrs rows row Hi_ptrs Hlen_rows).
      entailer!.
  - rewrite Zlength_replace_Znth.
    auto.
Qed.

End PtrArray2Lib.

End PtrArray2LibCoreSig.
