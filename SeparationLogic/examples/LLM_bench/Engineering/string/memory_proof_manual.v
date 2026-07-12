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
From SimpleC.EE.LLM_bench.Engineering.string Require Import memory_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Lemma proof_of_memcpy_entail_wit_1 : memcpy_entail_wit_1.
Proof.
  pre_process.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg dest_pre n_pre).
  change (sublist 0 0 bytes) with (@nil Z).
  rewrite (CharArray.full_empty dest_pre 0).
  split_pure_spatial.
  - cancel (CharArray.undef_seg dest_pre 0 n_pre).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_memcpy_entail_wit_2 : memcpy_entail_wit_2.
Proof.
  pre_process.
  replace (sublist 0 (i + 1) bytes)
    with (sublist 0 i bytes ++ Znth i bytes 0 :: nil).
  2: {
    rewrite (sublist_split 0 (i + 1) i bytes) by lia.
    rewrite (sublist_single 0 i bytes) by lia.
    reflexivity.
  }
  split_pure_spatial.
  - cancel (CharArray.full dest_pre (i + 1)
      (sublist 0 i bytes ++ Znth i bytes 0 :: nil)).
    cancel (CharArray.undef_seg dest_pre (i + 1) n_pre).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_memcpy_return_wit_1 : memcpy_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (HlenZ : Zlength bytes = n_pre) by lia.
  rewrite (sublist_self bytes n_pre) by exact (eq_sym HlenZ).
  rewrite (CharArray.undef_seg_empty dest_pre n_pre).
  split_pure_spatial.
  - cancel (CharArray.full dest_pre n_pre bytes).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_memmove_entail_wit_1 : memmove_entail_wit_1.
Proof.
  pre_process.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg dest_pre n_pre).
  change (sublist 0 0 bytes) with (@nil Z).
  rewrite (CharArray.full_empty dest_pre 0).
  split_pure_spatial.
  - cancel (CharArray.undef_seg dest_pre 0 n_pre).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_memmove_entail_wit_2 : memmove_entail_wit_2.
Proof.
  pre_process.
  replace (sublist 0 (i + 1) bytes)
    with (sublist 0 i bytes ++ Znth i bytes 0 :: nil).
  2: {
    rewrite (sublist_split 0 (i + 1) i bytes) by lia.
    rewrite (sublist_single 0 i bytes) by lia.
    reflexivity.
  }
  split_pure_spatial.
  - cancel (CharArray.full dest_pre (i + 1)
      (sublist 0 i bytes ++ Znth i bytes 0 :: nil)).
    cancel (CharArray.undef_seg dest_pre (i + 1) n_pre).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_memmove_entail_wit_3 : memmove_entail_wit_3.
Proof.
  pre_process.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg dest_pre n_pre).
  rewrite (Zsublist_nil bytes n_pre n_pre) by lia.
  replace (n_pre - n_pre) with 0 by lia.
  rewrite (CharArray.full_empty (dest_pre + n_pre * sizeof(CHAR)) 0).
  split_pure_spatial.
  - cancel (CharArray.undef_seg dest_pre 0 n_pre).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_memmove_entail_wit_4 : memmove_entail_wit_4.
Proof.
  pre_process.
  replace (sublist (i - 1) n_pre bytes)
    with ((Znth (i - 1) bytes 0 :: nil) ++ sublist i n_pre bytes).
  2: {
    rewrite (sublist_split (i - 1) n_pre i bytes) by lia.
    assert (Hsingle_bytes : sublist (i - 1) i bytes = Znth (i - 1) bytes 0 :: nil).
    {
      replace i with (i - 1 + 1) by lia.
      replace (i - 1 + 1 - 1) with (i - 1) by lia.
      apply sublist_single.
      lia.
    }
    rewrite Hsingle_bytes.
    reflexivity.
  }
  split_pure_spatial.
  - cancel (CharArray.undef_seg dest_pre 0 (i - 1)).
    cancel (CharArray.full src_pre n_pre bytes).
    replace (n_pre - (i - 1)) with (n_pre - i + 1) by lia.
    simpl. cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_memmove_return_wit_2 : memmove_return_wit_2.
Proof.
  pre_process.
  assert (Hi : i = 0) by lia.
  subst i.
  assert (HlenZ : Zlength bytes = n_pre) by lia.
  rewrite (sublist_self bytes n_pre) by exact (eq_sym HlenZ).
  replace (dest_pre + 0 * sizeof(CHAR)) with dest_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  rewrite (CharArray.undef_seg_empty dest_pre 0).
  split_pure_spatial.
  - cancel (CharArray.full dest_pre n_pre bytes).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_memmove_return_wit_1 : memmove_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (HlenZ : Zlength bytes = n_pre) by lia.
  rewrite (sublist_self bytes n_pre) by exact (eq_sym HlenZ).
  rewrite (CharArray.undef_seg_empty dest_pre n_pre).
  split_pure_spatial.
  - cancel (CharArray.full dest_pre n_pre bytes).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_memset_entail_wit_1 : memset_entail_wit_1.
Proof.
  pre_process.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg s_pre n_pre).
  unfold repeat_Z.
  simpl.
  rewrite (CharArray.full_empty s_pre 0).
  split_pure_spatial.
  - cancel (CharArray.undef_seg s_pre 0 n_pre).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_memset_entail_wit_2 : memset_entail_wit_2.
Proof.
  pre_process.
  rewrite repeat_Z_tail.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (i + 1) (repeat_Z c_pre i ++ c_pre :: nil)).
    cancel (CharArray.undef_seg s_pre (i + 1) n_pre).
  - split_pures; dump_pre_spatial; try lia; try assumption.
  - lia.
Qed.

Lemma proof_of_memset_return_wit_1 : memset_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  rewrite (CharArray.undef_seg_empty s_pre n_pre).
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre (repeat_Z c_pre n_pre)).
  - split_pures; dump_pre_spatial; reflexivity.
Qed.
