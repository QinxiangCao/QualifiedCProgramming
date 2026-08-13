Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import naive_C_Rules.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

From FP Require Import SetsFixedpoints.
From MonadLib Require Import MonadLib.
Import StateRelMonad.
From MonadLib.Examples Require Export mergesort.
Export MonadNotation.
Local Open Scope monad.
Local Open Scope sac.

Definition maketuple (x p :list Z): ((list Z) * (list Z)) := (x, p).
Definition applyf {A B: Type} (f: A -> B) (a: A) := f a.

Lemma int_array_merge_step_spatial_right : forall
  ret_pre arr_pre p_pre q_pre r_pre i j k
  l6_2 l5_2 l4_2 l1_2 l2_2 l3_2,
  IntArray.seg ret_pre p_pre (k + 1)
    (l3_2 ++ sublist 0 1 (replace_Znth 0 (Znth 0 l2_2 0) l6_2)) **
  (IntArray.seg ret_pre (k + 1) (r_pre + 1)
     (sublist 1 (r_pre + 1 - k) (replace_Znth 0 (Znth 0 l2_2 0) l6_2)) **
   (IntArray.seg arr_pre (q_pre + 1) (j + 1) (l5_2 ++ sublist 0 1 l2_2) **
    (IntArray.seg arr_pre (j + 1) (r_pre + 1) (sublist 1 (r_pre + 1 - j) l2_2) **
     (IntArray.seg arr_pre i (q_pre + 1) l1_2 **
      IntArray.seg arr_pre p_pre i l4_2)))) |--
  IntArray.seg arr_pre p_pre i l4_2 **
  IntArray.seg arr_pre i (q_pre + 1) l1_2 **
  IntArray.seg arr_pre (q_pre + 1) (j + 1) (l5_2 ++ sublist 0 1 l2_2) **
  IntArray.seg arr_pre (j + 1) (r_pre + 1) (sublist 1 (r_pre + 1 - j) l2_2) **
  IntArray.seg ret_pre p_pre (k + 1)
    (l3_2 ++ sublist 0 1 (replace_Znth 0 (Znth 0 l2_2 0) l6_2)) **
  IntArray.seg ret_pre (k + 1) (r_pre + 1)
    (sublist 1 (r_pre + 1 - k) (replace_Znth 0 (Znth 0 l2_2 0) l6_2)).
Proof.
  intros.
  cancel. cancel. cancel.
Qed.

Lemma int_array_merge_step_spatial_left : forall
  ret_pre arr_pre p_pre q_pre r_pre i j k
  l6_2 l5_2 l4_2 l1_2 l2_2 l3_2,
  IntArray.seg ret_pre p_pre (k + 1)
    (l3_2 ++ sublist 0 1 (replace_Znth 0 (Znth 0 l1_2 0) l6_2)) **
  (IntArray.seg ret_pre (k + 1) (r_pre + 1)
     (sublist 1 (r_pre + 1 - k) (replace_Znth 0 (Znth 0 l1_2 0) l6_2)) **
   (IntArray.seg arr_pre p_pre (i + 1) (l4_2 ++ sublist 0 1 l1_2) **
    (IntArray.seg arr_pre (i + 1) (q_pre + 1) (sublist 1 (q_pre + 1 - i) l1_2) **
     (IntArray.seg arr_pre j (r_pre + 1) l2_2 **
      IntArray.seg arr_pre (q_pre + 1) j l5_2)))) |--
  IntArray.seg arr_pre p_pre (i + 1) (l4_2 ++ sublist 0 1 l1_2) **
  IntArray.seg arr_pre (i + 1) (q_pre + 1) (sublist 1 (q_pre + 1 - i) l1_2) **
  IntArray.seg arr_pre (q_pre + 1) j l5_2 **
  IntArray.seg arr_pre j (r_pre + 1) l2_2 **
  IntArray.seg ret_pre p_pre (k + 1)
    (l3_2 ++ sublist 0 1 (replace_Znth 0 (Znth 0 l1_2 0) l6_2)) **
  IntArray.seg ret_pre (k + 1) (r_pre + 1)
    (sublist 1 (r_pre + 1 - k) (replace_Znth 0 (Znth 0 l1_2 0) l6_2)).
Proof.
  intros.
  cancel. cancel. cancel.
Qed.
