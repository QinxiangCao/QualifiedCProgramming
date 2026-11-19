(* Dynamic-frontier refinement; the high-level algorithm proofs are unchanged. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.stdlib.glibc Require Import two_way_dynamic_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.stdlib.glibc Require Import two_way_rel_lib.
From SimpleC.EE.stdlib.glibc Require Import two_way_critical_factorization_theorem.
From SimpleC.EE.stdlib.glibc Require Import two_way_match.
From SimpleC.EE.stdlib.glibc Require Import two_way_match_long_needle.
From SimpleC.EE.stdlib.glibc Require Import two_way_match_generic.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.



Require SimpleC.EE.stdlib.glibc.two_way_rel_proof_manual.
From SimpleC.EE.stdlib.glibc Require Import two_way_dynamic_lib.
Ltac tw_pose_shift_bound :=
  match goal with
  | Htable : shift_table_sound ?text ?pat ?tbl,
    Hlo : 0 <= Znth ?idx ?text 0,
    Hhi : Znth ?idx ?text 0 < 256 |- _ =>
      pose proof (tw_shift_table_bound pat tbl (Znth idx text 0)
        (proj1 Htable) (conj Hlo Hhi)) as Hprobe_shift_bound
  end.
Lemma proof_of_critical_factorization_entail_wit_1 : critical_factorization_entail_wit_1.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_entail_wit_1.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_entail_wit_2_1 : critical_factorization_entail_wit_2_1.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_entail_wit_2_1.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_entail_wit_2_2 : critical_factorization_entail_wit_2_2.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_entail_wit_2_2.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_entail_wit_2_3 : critical_factorization_entail_wit_2_3.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_entail_wit_2_3.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_entail_wit_2_4 : critical_factorization_entail_wit_2_4.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_entail_wit_2_4.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_entail_wit_3 : critical_factorization_entail_wit_3.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_entail_wit_3.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_entail_wit_4_1 : critical_factorization_entail_wit_4_1.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_entail_wit_4_1.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_entail_wit_4_2 : critical_factorization_entail_wit_4_2.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_entail_wit_4_2.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_entail_wit_4_3 : critical_factorization_entail_wit_4_3.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_entail_wit_4_3.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_entail_wit_4_4 : critical_factorization_entail_wit_4_4.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_entail_wit_4_4.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_return_wit_1 : critical_factorization_return_wit_1.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_return_wit_1.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_return_wit_2 : critical_factorization_return_wit_2.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_return_wit_2.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_safety_wit_65 : two_way_long_needle_safety_wit_65.
Proof.
pre_process.
  assert (0 < suffix).
  { destruct (Z_lt_le_dec 0 suffix); [assumption|].
    assert (suffix = 0) by lia; subst suffix.
    exfalso; apply PreH2.
    unfold memcmp_result, memcmp_eq in PreH3; apply PreH3.
    repeat rewrite Zsublist_nil by lia; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_1 : two_way_long_needle_entail_wit_1.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("shift_table")) 256).
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  rewrite IntArray.seg_empty.
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_2 : two_way_long_needle_entail_wit_2.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  change (Z.shiftl 1 8) with 256 in *.
  rewrite repeat_Z_tail; try lia.
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_3 : two_way_long_needle_entail_wit_3.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (i >= (Z.shiftl 1 8))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (0 <= i)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (i <= 256)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (0 < mp)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (mp <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : ((mp + suffix ) <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  change (Z.shiftl 1 8) with 256 in H.
  assert (i = 256) by lia.
  subst i.
  Exists (repeat_Z needle_len_pre 256).
  sep_apply (store_int_undef_store_int (&("i")) 256).
  rewrite IntArray.undef_seg_empty.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  split_pure_spatial.
  - unfold IntArray.full, IntArray.seg, store_array; cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  unfold shift_table_build_prefix.
  repeat split; try lia; try apply Zlength_nonneg;
    try (unfold repeat_Z; rewrite Zlength_correct, repeat_length; lia).
  intros c Hc.
  right; split;
    [ intros idx Hidx; lia
    | unfold repeat_Z;
      rewrite Znth_repeat_lt; try lia;
      match goal with
      | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ =>
          rewrite Hlen
      end;
      reflexivity ].
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_4 : two_way_long_needle_entail_wit_4.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  prop_apply (UCharArray_full_Znth_range needle_pre needle_len_pre needle0_low_level_spec 0 ltac:(lia)).
  Intros.
  Exists table_2.
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_6 : two_way_long_needle_entail_wit_6.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  Exists (replace_Znth (Znth i needle0_low_level_spec 0) (needle_len_pre - i - 1) table_2).
  try rewrite replace_Znth_Znth by tauto.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  prop_apply (UCharArray_full_Znth_range_le needle_pre needle_len_pre needle0_low_level_spec (i + 1) ltac:(lia)).
  Intros.
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  replace (needle_len_pre - i - 1) with (Zlength needle0_low_level_spec - i - 1) by lia.
  apply shift_table_build_prefix_step; try lia; assumption.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_7 : two_way_long_needle_entail_wit_7.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (i >= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (shift_table_build_prefix needle0_low_level_spec i table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (0 <= i)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (i <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (0 <= (Znth (i) (needle0_low_level_spec) (0)))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : ((Znth (i) (needle0_low_level_spec) (0)) < 256)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (0 < mp)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (mp <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : ((mp + suffix ) <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  assert (i = needle_len_pre) by lia.
  subst i.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  prop_apply
    (UCharArray_full_all_Znth_range
       haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  assert (Hhay_range :
    forall q, 0 <= q < Zlength hay0_low_level_spec ->
      0 <= Znth q hay0_low_level_spec 0 < 256) by assumption.
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("i")) needle_len_pre).
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  eapply shift_table_build_prefix_sound.
  - lia.
  - exact Hhay_range.
  - replace (Zlength needle0_low_level_spec) with needle_len_pre by lia.
    exact H2.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_8 : two_way_long_needle_entail_wit_8.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (retval = 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (memcmp_result needle0_low_level_spec 0 mp suffix retval )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (INT_MIN <= retval)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (retval <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (0 < mp)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (mp <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : ((mp + suffix ) <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  Exists table_2.
  split_pure_spatial; [entailer! |].
  assert (Hrep : repetitive_split needle0_low_level_spec suffix mp).
  { unfold repetitive_split, memcmp_result, memcmp_eq in *.
    pose proof (proj1 H0 H) as Htmp.
    rewrite Z.add_0_l in Htmp.
    replace (suffix + mp) with (mp + suffix) by lia.
    exact Htmp. }
  split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - match goal with Hsafe : safeExec _ _ _ |- _ =>
      unfold applyf, maketuple, two_way_generic_after_factorization, generic_match_phase in Hsafe;
      prog_nf in Hsafe; safe_choice_l Hsafe; exact Hsafe end.
  - unfold periodic_memory_match.
    split; [exact (proj1 (H4 Hrep)) | split; [left; reflexivity | reflexivity]].
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_11 : two_way_long_needle_entail_wit_11.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  prop_apply (UCharArray_full_Znth_range haystack_pre hn_low_level_spec hay0_low_level_spec (j + needle_len_pre - 1) ltac:(lia)).
  Intros.
  Exists table_2.
  sep_apply_l_atomic (UCharArray.full_split_to_missing_i haystack_pre (j + needle_len_pre - 1) hn_low_level_spec hay0_low_level_spec 0 ltac:(lia)).
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_12_1 : two_way_long_needle_entail_wit_12_1.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  try rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hskip : valid_skip hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - mp)).
  {
    replace (needle_len_pre - mp) with (Zlength needle0_low_level_spec - mp) by lia.
    eapply (long_needle_periodic_memory_skip_valid
              hay0_low_level_spec needle0_low_level_spec j 0 mp memory table_2);
      try eassumption; try lia.
    - unfold repetitive_split.
      rewrite !Zsublist_nil by lia.
      reflexivity.
    - match goal with Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => rewrite Hlen; lia end.
  }
  Exists table_2.
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  unfold valid_skip in Hskip.
  lia.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_12_2 : two_way_long_needle_entail_wit_12_2.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  try rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  Exists table.
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  match goal with Htable : shift_table_sound _ _ _ |- _ => destruct Htable as [_ Hsound] end.
  specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) table 0)).
  specialize (Hsound ltac:(split; try lia)).
  specialize (Hsound ltac:(replace (Zlength needle0_low_level_spec) with needle_len_pre by lia; reflexivity)).
  destruct Hsound as [[Hz _] | Hskip].
  - lia.
  - exact Hskip.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_12_3 : two_way_long_needle_entail_wit_12_3.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  try rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  Exists table.
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  match goal with Htable : shift_table_sound _ _ _ |- _ => destruct Htable as [_ Hsound] end.
  specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) table 0)).
  specialize (Hsound ltac:(split; try lia)).
  specialize (Hsound ltac:(replace (Zlength needle0_low_level_spec) with needle_len_pre by lia; reflexivity)).
  destruct Hsound as [[Hz _] | Hskip].
  - exfalso; lia.
  - exact Hskip.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_13 : two_way_long_needle_entail_wit_13.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  try rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = hn_low_level_spec).
  {
    match goal with
    | Hlen : Zlength hay0_low_level_spec = hn_low_level_spec |- _ => exact Hlen
    end.
  }
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  match goal with
  | Htable : shift_table_sound hay0_low_level_spec needle0_low_level_spec ?tbl |- _ =>
      assert (Hshift_match :
        Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) tbl 0 = 0 /\
        match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1));
      [ destruct Htable as [_ Hsound];
        specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) tbl 0));
        specialize (Hsound ltac:(rewrite Hneedle_len, Hhay_len; split; try lia));
        specialize (Hsound ltac:(rewrite Hneedle_len; reflexivity));
        destruct Hsound as [Hzm | Hskip];
        [ destruct Hzm as [Hz Hmatch];
          split; [exact Hz |];
          rewrite Hneedle_len in Hmatch;
          exact Hmatch
        | unfold valid_skip in Hskip;
          lia ]
      | Exists tbl ]
  end.
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_14_1 : two_way_long_needle_entail_wit_14_1.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec); Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec); Intros.
  Exists table_2.
  split_pure_spatial.
  - sep_apply (store_int_undef_store_int (&("shift"))); cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + match goal with HH : safeExec _ _ _ |- _ => rename HH into Hsafe end.
        unfold generic_match_periodic_from in Hsafe at 1;
        unfold_loop in Hsafe; prog_nf in Hsafe;
        unfold generic_match_periodic_loop_body in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_r Hsafe;
        unfold match_periodic_loop_body in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_l Hsafe;
        try (match goal with Hn : Zlength needle0_low_level_spec = needle_len_pre,
                             Hh : Zlength hay0_low_level_spec = hn_low_level_spec |- _ => rewrite Hn, Hh; lia end);
        replace (Z.max suffix memory) with suffix in Hsafe by lia;
        unfold generic_match_periodic_from_right, generic_match_periodic_from;
        prog_nf; eapply safeExec_proequiv; [| exact Hsafe];
        apply common_step_equiv; intros [[pos2 mem2] | res]; simpl; reflexivity
      .
    + unfold matched_range; intros k Hk; lia.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_14_2 : two_way_long_needle_entail_wit_14_2.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec); Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec); Intros.
  Exists table_2.
  split_pure_spatial.
  - sep_apply (store_int_undef_store_int (&("shift"))); cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + match goal with HH : safeExec _ _ _ |- _ => rename HH into Hsafe end.
        unfold generic_match_periodic_from in Hsafe at 1;
        unfold_loop in Hsafe; prog_nf in Hsafe;
        unfold generic_match_periodic_loop_body in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_r Hsafe;
        unfold match_periodic_loop_body in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_l Hsafe;
        try (match goal with Hn : Zlength needle0_low_level_spec = needle_len_pre,
                             Hh : Zlength hay0_low_level_spec = hn_low_level_spec |- _ => rewrite Hn, Hh; lia end);
        replace (Z.max suffix memory) with memory in Hsafe by lia;
        unfold generic_match_periodic_from_right, generic_match_periodic_from;
        prog_nf; eapply safeExec_proequiv; [| exact Hsafe];
        apply common_step_equiv; intros [[pos2 mem2] | res]; simpl; reflexivity
      .
    + unfold matched_range, match_cond; intros k Hk.
      match goal with Hmem : periodic_memory_match _ _ _ _ _ |- _ =>
        destruct Hmem as [_ [_ Hmem]];
        apply (f_equal (fun xs => Znth k xs 0)) in Hmem;
        rewrite Znth_sublist0 in Hmem by lia;
        rewrite Znth_sublist in Hmem by lia;
        replace (k + j) with (j + k) in Hmem by lia; exact Hmem
      end.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_15 : two_way_long_needle_entail_wit_15.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec); Intros.
  Exists table_2.
  split_pure_spatial.
  - replace (needle_pre + (i + 1) * sizeof(UCHAR))
      with (needle_pre + i * sizeof(UCHAR) + 1 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    replace (haystack_pre + (i + 1 + j) * sizeof(UCHAR))
      with (haystack_pre + (i + j) * sizeof(UCHAR) + 1 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    entailer!.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + match goal with HH : safeExec _ _ _ |- _ => rename HH into Hsafe end.
        unfold generic_match_periodic_from_right, match_periodic_from_right in Hsafe;
        prog_nf in Hsafe; unfold match_right in Hsafe at 1;
        unfold_loop in Hsafe; prog_nf in Hsafe;
        unfold match_right_f in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_l Hsafe;
        [ unfold continue in Hsafe; prog_nf in Hsafe;
          unfold generic_match_periodic_from_right, match_periodic_from_right, match_right;
          prog_nf; exact Hsafe
        | split; [match goal with Hn : Zlength needle0_low_level_spec = needle_len_pre |- _ => rewrite Hn; lia end | unfold match_cond; replace (j+i) with (i+j) by lia; assumption] ]
      .
    + unfold matched_range in *; intros k Hk.
      destruct (Z.eq_dec k i) as [Heq | Hneq].
      * subst k; unfold match_cond; replace (j+i) with (i+j) by lia; assumption.
      * match goal with Hr : forall k : Z, _ -> match_cond _ _ _ k |- _ => apply Hr; lia end.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_16 : two_way_long_needle_entail_wit_16.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec); Intros.
  assert (Hlen : Zlength needle0_low_level_spec = needle_len_pre) by assumption.
  assert (i = needle_len_pre - 1) by lia; subst i.
  Exists table_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try assumption; try lia.
  - match goal with HH : safeExec _ _ _ |- _ => rename HH into Hsafe end.
    unfold generic_match_periodic_from_right, match_periodic_from_right in Hsafe;
    prog_nf in Hsafe; unfold match_right in Hsafe at 1;
    unfold_loop in Hsafe; prog_nf in Hsafe;
    unfold match_right_f in Hsafe at 1; prog_nf in Hsafe;
    safe_choice_l Hsafe.
    2: { split; [lia | assumption]. }
    unfold continue in Hsafe; prog_nf in Hsafe.
    replace (needle_len_pre - 1 + 1) with needle_len_pre in Hsafe by lia.
    unfold_loop in Hsafe; prog_nf in Hsafe;
    unfold match_right_f in Hsafe at 1; prog_nf in Hsafe;
    safe_choice_r Hsafe.
    2: { left; lia. }
    unfold break in Hsafe; prog_nf in Hsafe;
    unfold match_periodic_after_right in Hsafe at 1; prog_nf in Hsafe;
    safe_choice_l Hsafe; try (rewrite Hlen; reflexivity).
    unfold generic_match_periodic_from_left; exact Hsafe.
  - unfold matched_range in *; intros k Hk.
    destruct (Z.eq_dec k (needle_len_pre-1)).
    + subst k; assumption.
    + match goal with Hr : forall k : Z, _ -> match_cond _ _ _ k |- _ => apply Hr; lia end.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_17 : two_way_long_needle_entail_wit_17.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec); Intros.
  Exists table_2.
  split_pure_spatial.
  - replace (needle_pre + i * sizeof(UCHAR) - 1 * sizeof(UCHAR))
      with (needle_pre + (i - 1) * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    replace (haystack_pre + (i + j) * sizeof(UCHAR) - 1 * sizeof(UCHAR))
      with (haystack_pre + (i - 1 + j) * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    entailer!.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + match goal with HH : safeExec _ _ _ |- _ => rename HH into Hsafe end.
        unfold generic_match_periodic_from_left, match_periodic_from_left in Hsafe;
        prog_nf in Hsafe; unfold match_left in Hsafe at 1;
        unfold_loop in Hsafe; prog_nf in Hsafe;
        unfold match_left_f in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_l Hsafe;
        [ unfold continue in Hsafe; prog_nf in Hsafe;
          unfold generic_match_periodic_from_left, match_periodic_from_left, match_left;
          prog_nf; exact Hsafe
        | split; [lia | unfold match_cond; replace (j+i) with (i+j) by lia; assumption] ]
      .
    + unfold matched_range in *; intros k Hk.
      destruct (Z.eq_dec k i) as [Heq | Hneq].
      * subst k; unfold match_cond; replace (j+i) with (i+j) by lia; assumption.
      * match goal with Hr : forall k : Z, _ -> match_cond _ _ _ k |- _ => apply Hr; lia end.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_18 : two_way_long_needle_entail_wit_18.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  Exists table_2.
  sep_apply (store_ptr_undef_store_ptr (&("pneedle"))
    (needle_pre + i * sizeof(UCHAR))).
  sep_apply (store_ptr_undef_store_ptr (&("phaystack"))
    (haystack_pre + (i + j) * sizeof(UCHAR))).
  sep_apply (IntArray.full_to_undef_full (&("shift_table")) 256 table_2).
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_19_1 : two_way_long_needle_entail_wit_19_1.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : ((i + 1 ) >= (memory + 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (memory < (i + 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (repetitive_split needle0_low_level_spec suffix mp )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (j <= (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (0 < mp)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : (mp <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H17 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H18 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H19 : (0 <= memory)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H20 : (memory < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H21 : (0 <= (i + 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H22 : ((i + 1 ) <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("i")) i).
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  {
    unfold periodic_memory_match.
    split.
    - exact (proj1 (H3 H4)).
    - split.
      + right. lia.
      + apply (proj2 (list_eq_ext _ _ 0)).
        split.
        * rewrite !Zlength_sublist by (split; lia). lia.
        * intros q Hq.
          assert (Hqlen : q < needle_len_pre - mp).
          { rewrite Zlength_sublist in Hq by (split; lia). lia. }
          rewrite Znth_sublist0 by lia.
          rewrite Znth_sublist by lia.
          pose proof (proj1 (H3 H4)) as Hperiod.
          destruct Hperiod as [_ Hperiod].
          rewrite (Hperiod q ltac:(lia) ltac:(lia)).
          unfold matched_range, match_cond in H6.
          pose proof (proj2 (H3 H4)) as Hcut.
          specialize (H6 (q + mp) ltac:(lia)).
          replace (q + (j + mp)) with (j + (q + mp)) by lia.
          exact H6.
  }
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_periodic_from_left in Hexec. prog_nf in Hexec.
  unfold match_periodic_from_left in Hexec. prog_nf in Hexec.
  unfold match_left in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold match_left_f in Hexec at 1.
  prog_nf in Hexec.
  safe_choice_r Hexec.
  - prog_nf in Hexec.
    unfold match_periodic_after_left in Hexec. prog_nf in Hexec.
    unfold break in Hexec. prog_nf in Hexec.
    safe_choice_r Hexec; try lia.
    unfold continue in Hexec.
    prog_nf in Hexec.
    replace ((Zlength needle0_low_level_spec - mp)) with ((needle_len_pre - mp)) in Hexec by lia.
    exact Hexec.
  - right. unfold match_cond.
    replace (j + i) with (i + j) by lia.
    exact H0.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_19_2 : two_way_long_needle_entail_wit_19_2.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : ((needle_len_pre - 1 ) > i)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (i < (needle_len_pre - 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (repetitive_split needle0_low_level_spec suffix mp )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (j <= (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : (0 < mp)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H17 : (mp <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H18 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H19 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H20 : (0 <= memory)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H21 : (memory < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H22 : (suffix <= i)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H23 : (memory <= i)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H24 : (i <= (needle_len_pre - 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("i")) i).
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  - unfold periodic_memory_match.
    split; [exact (proj1 (H3 H4)) |].
    split; [left; reflexivity |].
    rewrite !Zsublist_nil by lia.
    reflexivity.
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_periodic_from_right in Hexec. prog_nf in Hexec.
    unfold match_periodic_from_right in Hexec. prog_nf in Hexec.
    unfold match_right in Hexec. prog_nf in Hexec.
    unfold_loop in Hexec. prog_nf in Hexec.
    unfold match_right_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec.
    + prog_nf in Hexec.
      unfold break in Hexec.
      prog_nf in Hexec.
      unfold match_periodic_after_right in Hexec. prog_nf in Hexec.
      safe_choice_r Hexec; try lia.
      unfold continue in Hexec.
      prog_nf in Hexec.
      replace (j + (i - suffix + 1)) with (j + i - suffix + 1) by lia.
      exact Hexec.
    + right. unfold match_cond.
      replace (j + i) with (i + j) by lia.
      exact H0.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_19_3 : two_way_long_needle_entail_wit_19_3.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (repetitive_split needle0_low_level_spec suffix mp )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (valid_skip hay0_low_level_spec needle0_low_level_spec j shift )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (j <= (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (0 < shift)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (0 < mp)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (mp <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hskip_bound_len : j + shift <= hn_low_level_spec).
  {
    pose proof H3 as Hskip.
    unfold valid_skip in Hskip.
    destruct Hskip as [_ [Hbound _]].
    rewrite H17 in Hbound.
    exact Hbound.
  }
  assert (Hloop_bound_len :
    j + Zlength needle0_low_level_spec <= Zlength hay0_low_level_spec).
  {
    rewrite H17, H18.
    lia.
  }
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("shift"))).
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  - unfold periodic_memory_match.
    split; [exact (proj1 (H0 H1)) |].
    split; [left; reflexivity |].
    rewrite !Zsublist_nil by lia.
    reflexivity.
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_periodic_from in Hexec. prog_nf in Hexec.
    unfold_loop in Hexec. prog_nf in Hexec.
    unfold generic_match_periodic_loop_body in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec.
    + prog_nf in Hexec. eapply (@safeExec_any_bind _ _ Z _ _ _ shift) in Hexec.
        safe_step Hexec.
        unfold continue in Hexec.
        prog_nf in Hexec.
        unfold generic_match_periodic_from.
        exact Hexec.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_20_1 : two_way_long_needle_entail_wit_20_1.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (suffix > (needle_len_pre - suffix ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (retval <> 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (memcmp_result needle0_low_level_spec 0 mp suffix retval )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (INT_MIN <= retval)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (retval <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (0 < mp)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (mp <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : ((mp + suffix ) <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table_2.
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold applyf, maketuple in Hexec. prog_nf in Hexec.
  simpl in Hexec.
  unfold generic_match_phase in Hexec.
  prog_nf in Hexec.
  safe_choice_r Hexec.
  - replace (Z.max suffix (Zlength needle0_low_level_spec - suffix) + 1)
      with (suffix + 1) in Hexec by (rewrite Hneedle_len; lia).
    exact Hexec.
  - unfold repetitive_split, memcmp_result, memcmp_eq in *.
    intro Hr.
    apply H0.
    apply H1.
    replace (0 + suffix) with suffix by lia.
    replace (mp + suffix) with (suffix + mp) by lia.
    exact Hr.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_20_2 : two_way_long_needle_entail_wit_20_2.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (suffix <= (needle_len_pre - suffix ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (retval <> 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (memcmp_result needle0_low_level_spec 0 mp suffix retval )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (INT_MIN <= retval)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (retval <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (0 < mp)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (mp <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : ((mp + suffix ) <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table_2.
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  - assert (1 <= suffix) by (
      unfold memcmp_result, memcmp_eq in H1;
      destruct (Z.eq_dec suffix 0); subst;
      [ exfalso; apply H0; apply H1; rewrite !Zsublist_nil by lia; reflexivity
      | lia ]).
    lia.
  - assert (1 <= suffix) by (
      unfold memcmp_result, memcmp_eq in H1;
      destruct (Z.eq_dec suffix 0); subst;
      [ exfalso; apply H0; apply H1; rewrite !Zsublist_nil by lia; reflexivity
      | lia ]).
    lia.
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold applyf, maketuple in Hexec. prog_nf in Hexec.
    simpl in Hexec.
    unfold generic_match_phase in Hexec.
    prog_nf in Hexec.
    safe_choice_r Hexec.
    + replace (Z.max suffix (Zlength needle0_low_level_spec - suffix) + 1)
        with (needle_len_pre - suffix + 1) in Hexec by (rewrite Hneedle_len; lia).
      exact Hexec.
    + unfold repetitive_split, memcmp_result, memcmp_eq in *.
      intro Hr.
      apply H0.
      apply H1.
      replace (0 + suffix) with suffix by lia.
      replace (mp + suffix) with (suffix + mp) by lia.
      exact Hr.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_23 : two_way_long_needle_entail_wit_23.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  prop_apply (UCharArray_full_Znth_range haystack_pre hn_low_level_spec hay0_low_level_spec (j + needle_len_pre - 1) ltac:(lia)).
  Intros.
  Exists table_2.
  sep_apply_l_atomic (UCharArray.full_split_to_missing_i haystack_pre (j + needle_len_pre - 1) hn_low_level_spec hay0_low_level_spec 0 ltac:(lia)).
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_24 : two_way_long_needle_entail_wit_24.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (0 < (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (j <= (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (0 <= ((j + needle_len_pre ) - 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (((j + needle_len_pre ) - 1 ) < hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (0 < suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : (0 < period)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H17 : (period <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  try rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = hn_low_level_spec).
  {
    match goal with
    | Hlen : Zlength hay0_low_level_spec = hn_low_level_spec |- _ => exact Hlen
    end.
  }
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table.
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  match goal with Htab : shift_table_sound _ _ _ |- _ => destruct Htab as [_ Hsound] end.
  specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) table 0)).
  specialize (Hsound ltac:(split; [lia | rewrite Hhay_len, Hneedle_len; lia])
    ltac:(rewrite Hneedle_len; reflexivity)).
  destruct Hsound as [[Hz _] | Hskip].
  - rewrite Hz in H. lia.
  - exact Hskip.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_25 : two_way_long_needle_entail_wit_25.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  try rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = hn_low_level_spec).
  {
    match goal with
    | Hlen : Zlength hay0_low_level_spec = hn_low_level_spec |- _ => exact Hlen
    end.
  }
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table.
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  - match goal with Htab : shift_table_sound _ _ _ |- _ => destruct Htab as [_ Hsound] end.
    specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) table 0)).
    specialize (Hsound ltac:(split; [lia | rewrite Hhay_len, Hneedle_len; lia])
      ltac:(rewrite Hneedle_len; reflexivity)).
    destruct Hsound as [[_ Hmatch] | Hskip].
    + rewrite Hneedle_len in Hmatch. exact Hmatch.
    + unfold valid_skip in Hskip. lia.

Qed.

Lemma proof_of_two_way_long_needle_entail_wit_26 : two_way_long_needle_entail_wit_26.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = hn_low_level_spec).
  {
    match goal with
    | Hlen : Zlength hay0_low_level_spec = hn_low_level_spec |- _ => exact Hlen
    end.
  }
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("shift"))).
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold generic_match_loop_body in Hexec at 1.
  prog_nf in Hexec.
  apply safeExec_choice_r in Hexec.
  unfold match_loop_body in Hexec at 1; prog_nf in Hexec.
  safe_choice_l Hexec; [|rewrite Hneedle_len,Hhay_len;lia].
  unfold generic_match_from_right.
  prog_nf in Hexec.
  eapply safeExec_proequiv; [|exact Hexec].
  unfold generic_match_after_right, generic_match_from_left,
    generic_match_after_left, generic_match_from, continue, break.
  repeat first [reflexivity | progress prog_nf | apply common_step_equiv; intro | apply choice_case_equiv].
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_27 : two_way_long_needle_entail_wit_27.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (i < (needle_len_pre - 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (j <= (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (0 < suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (suffix <= i)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (i <= (needle_len_pre - 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : (0 <= (i + j ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H17 : ((i + j ) < hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H18 : (0 < period)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H19 : (period <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table_2.
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
    unfold generic_match_from_right in Hexec at 1; prog_nf in Hexec.
    unfold match_right in Hexec at 1; prog_nf in Hexec.
    unfold_loop in Hexec; prog_nf in Hexec.
    unfold match_right_f in Hexec at 1; prog_nf in Hexec.
    safe_choice_l Hexec.
    + unfold continue in Hexec at 1; prog_nf in Hexec.
      unfold generic_match_from_right.
      unfold match_right.
      exact Hexec.
    + split.
      * rewrite Hneedle_len; lia.
      * unfold match_cond.
        replace (j + i) with (i + j) by lia.
        exact H.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_28 : two_way_long_needle_entail_wit_28.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  assert (i = needle_len_pre - 1) by lia.
  subst i.
  Exists table_2.
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].

  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from_right in Hexec. prog_nf in Hexec.
  unfold match_right in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold match_right_f in Hexec at 1.
  prog_nf in Hexec.
  safe_choice_l Hexec.
  2: { split; [rewrite Hneedle_len; lia |].
       match goal with Hlast : match_cond _ _ _ (needle_len_pre - 1) |- _ => exact Hlast end. }
  unfold continue in Hexec at 1; prog_nf in Hexec.
  replace (needle_len_pre - 1 + 1) with needle_len_pre in Hexec by lia.
  unfold_loop in Hexec; prog_nf in Hexec.
  unfold match_right_f in Hexec at 1; prog_nf in Hexec.
  safe_choice_r Hexec; [|left; rewrite Hneedle_len;lia].
  unfold break in Hexec at 1; prog_nf in Hexec.
  unfold generic_match_after_right in Hexec at 1; prog_nf in Hexec.
  safe_choice_l Hexec; try lia.
  exact Hexec.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_29 : two_way_long_needle_entail_wit_29.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (i <> (-1))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (j <= (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (0 < suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (0 <= (i + 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : ((i + 1 ) <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (0 <= ((i + 1 ) + j ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : (((i + 1 ) + j ) <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H17 : (0 < period)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H18 : (period <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  Exists table_2.
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
    unfold generic_match_from_left in Hexec at 1.
    prog_nf in Hexec.
    unfold match_left in Hexec at 1.
    prog_nf in Hexec.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_left_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec.
    + unfold continue in Hexec at 1.
      prog_nf in Hexec.
      unfold generic_match_from_left.
      prog_nf.
      unfold match_left.
      exact Hexec.
    + split.
      * lia.
      * unfold match_cond.
        replace (j + i) with (i + j) by lia.
        exact H.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_30_1 : two_way_long_needle_entail_wit_30_1.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (i <> (-1))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (i <> (-1))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (j <= (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (0 < suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (0 <= (i + 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : ((i + 1 ) <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : (0 <= ((i + 1 ) + j ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H17 : (((i + 1 ) + j ) <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H18 : (0 < period)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H19 : (period <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("i")) i).
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from_left in Hexec at 1.
  prog_nf in Hexec.
  unfold match_left in Hexec at 1.
  prog_nf in Hexec.
  unfold_loop in Hexec.
  prog_nf in Hexec.
  unfold match_left_f in Hexec at 1.
  prog_nf in Hexec.
  safe_choice_r Hexec.
  - unfold break in Hexec at 1.
    prog_nf in Hexec.
    unfold generic_match_after_left in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec; try lia.
    exact Hexec.
  - right.
    unfold match_cond.
    replace (j + i) with (i + j) by lia.
    exact H0.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_30_2 : two_way_long_needle_entail_wit_30_2.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : ((needle_len_pre - 1 ) > i)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (i < (needle_len_pre - 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (j <= (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (0 < suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (suffix <= i)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : (i <= (needle_len_pre - 1 ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H17 : (0 <= (i + j ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H18 : ((i + j ) < hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H19 : (0 < period)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H20 : (period <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("i")) i).
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from_right in Hexec. prog_nf in Hexec.
    unfold match_right in Hexec. prog_nf in Hexec.
    unfold_loop in Hexec. prog_nf in Hexec.
    unfold match_right_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec.
    + prog_nf in Hexec.
      unfold break in Hexec.
      prog_nf in Hexec.
      unfold generic_match_after_right in Hexec. prog_nf in Hexec.
      safe_choice_r Hexec; try lia.
      unfold continue in Hexec.
      prog_nf in Hexec.
      replace (j + (i - suffix + 1)) with (j + i - suffix + 1) by lia.
      exact Hexec.
      all: try lia.
      all: try (match goal with
        | Hlen : Zlength ?xs = ?n |- _ =>
            rewrite Hlen; lia
        end).
    + right. unfold match_cond.
      replace (j + i) with (i + j) by lia.
      exact H0.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_30_3 : two_way_long_needle_entail_wit_30_3.
Proof.
pre_process.
  try tw_pose_shift_bound.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (valid_skip hay0_low_level_spec needle0_low_level_spec j shift )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (j <= (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (0 < shift)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (0 < suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (0 < period)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (period <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hskip_bound_len : j + shift <= hn_low_level_spec).
  {
    pose proof H0 as Hskip.
    unfold valid_skip in Hskip.
    destruct Hskip as [_ [Hbound _]].
    match goal with
    | Hlen : Zlength hay0_low_level_spec = hn_low_level_spec |- _ =>
        rewrite <- Hlen; exact Hbound
    end.
  }
  assert (Hloop_bound_len :
    j + Zlength needle0_low_level_spec <= Zlength hay0_low_level_spec).
  {
    match goal with
    | Hhay : Zlength hay0_low_level_spec = hn_low_level_spec,
      Hneedle : Zlength needle0_low_level_spec = needle_len_pre |- _ =>
        rewrite Hhay, Hneedle; lia
    end.
  }
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("shift"))).
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from in Hexec. prog_nf in Hexec.
    unfold_loop in Hexec. prog_nf in Hexec.
    unfold generic_match_loop_body in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec.
    + prog_nf in Hexec. eapply (@safeExec_any_bind _ _ Z _ _ _ shift) in Hexec.
        safe_step Hexec.
        unfold continue in Hexec.
        prog_nf in Hexec.
        unfold generic_match_from.
        exact Hexec.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_return_wit_1 : two_way_long_needle_return_wit_1.
Proof.
pre_process.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (j > (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (repetitive_split needle0_low_level_spec suffix mp )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (j <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (0 < mp)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (mp <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H14 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H15 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H16 : (0 <= memory)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H17 : (memory < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = hn_low_level_spec) by
    (match goal with Hlen : Zlength hay0_low_level_spec = hn_low_level_spec |- _ => exact Hlen end).
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre) by
    (match goal with Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen end).
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  unfold generic_match_periodic_from in H0.
  unfold_loop in H0.
  unfold generic_match_periodic_loop_body in H0 at 1.
  prog_nf in H0.
  safe_choice_r H0.
  unfold match_periodic_loop_body in H0 at 1; prog_nf in H0.
  safe_choice_r H0; try (rewrite Hneedle_len, Hhay_len; lia).
  unfold break in H0.
  prog_nf in H0.
  unfold uchar_ptr_option_repr.
  simpl.
  exact H0.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_return_wit_2 : two_way_long_needle_return_wit_2.
Proof.
pre_process.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
    assert (H : (j > (hn_low_level_spec - needle_len_pre ))) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H0 : (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H1 : (shift_table_sound hay0_low_level_spec needle0_low_level_spec table )) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H2 : (haystack_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H3 : (needle_pre > 0)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H4 : (32 < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H5 : (needle_len_pre <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H6 : (hn_low_level_spec <= INT_MAX)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H7 : (0 <= j)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H8 : (j <= hn_low_level_spec)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H9 : (0 < suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H10 : (0 <= suffix)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H11 : (suffix < needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H12 : (0 < period)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
    assert (H13 : (period <= needle_len_pre)) by (first [assumption | lia | congruence | (rewrite ?sizeof_uchar; lia)]).
  prop_apply (UCharArray.full_Zlength haystack_pre hn_low_level_spec hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = hn_low_level_spec) by
    (match goal with Hlen : Zlength hay0_low_level_spec = hn_low_level_spec |- _ => exact Hlen end).
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre) by
    (match goal with Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen end).
  try split_pure_spatial; try solve [entailer!]; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  unfold generic_match_from in H0.
  unfold_loop in H0.
  unfold generic_match_loop_body in H0 at 1.
  prog_nf in H0.
  safe_choice_r H0.
  unfold match_loop_body in H0 at 1; prog_nf in H0.
  safe_choice_r H0; try (rewrite Hneedle_len, Hhay_len; lia).
  unfold break in H0.
  prog_nf in H0.
  unfold uchar_ptr_option_repr.
  simpl.
  exact H0.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_return_wit_3 : two_way_long_needle_return_wit_3.
Proof.
pre_process.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  subst i.
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from_left in Hexec. prog_nf in Hexec.
  unfold match_left in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold match_left_f in Hexec at 1.
  prog_nf in Hexec.
  safe_choice_r Hexec; try lia.
  unfold break in Hexec.
  prog_nf in Hexec.
  unfold generic_match_after_left in Hexec. prog_nf in Hexec.
  safe_choice_l Hexec; try lia.
  unfold break in Hexec.
  prog_nf in Hexec.
  unfold uchar_ptr_option_repr.
  rewrite sizeof_uchar.
  destruct (Z.eq_dec (haystack_pre + j * 1) NULL) as [Heq | Hneq].
  - change (haystack_pre + j * 1 = 0) in Heq.
    lia.
  - rewrite Z.div_1_r.
    replace (haystack_pre + j * 1 - haystack_pre) with j by lia.
    exact Hexec.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_return_wit_4 : two_way_long_needle_return_wit_4.
Proof.
pre_process.
    try replace (i + j + 1) with (i + 1 + j) by lia.
    try replace (i + j + -1) with (i - 1 + j) by lia.
    try replace (i + -1) with (i - 1) by lia.
  first [split_pure_spatial; [try solve [entailer!] | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | entailer!].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_periodic_from_left in Hexec. prog_nf in Hexec.
  unfold match_periodic_from_left in Hexec. prog_nf in Hexec.
  unfold match_left in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold match_left_f in Hexec at 1.
  prog_nf in Hexec.
  safe_choice_r Hexec; try lia.
  unfold break in Hexec.
  prog_nf in Hexec.
  unfold match_periodic_after_left in Hexec. prog_nf in Hexec.
  safe_choice_l Hexec; try lia.
  unfold break in Hexec.
  prog_nf in Hexec.
  unfold uchar_ptr_option_repr.
  rewrite sizeof_uchar.
  destruct (Z.eq_dec (haystack_pre + j * 1) NULL) as [Heq | Hneq].
  - change (haystack_pre + j * 1 = 0) in Heq.
    lia.
  - rewrite Z.div_1_r.
    replace (haystack_pre + j * 1 - haystack_pre) with j by lia.
    exact Hexec.
all: try entailer!.
Qed.

Lemma proof_of_two_way_long_needle_partial_solve_wit_1_pure : two_way_long_needle_partial_solve_wit_1_pure.
Proof.
pre_process.
Qed.

Lemma proof_of_two_way_long_needle_low_level_spec_entail_high_level_spec : two_way_long_needle_low_level_spec_entail_high_level_spec.
Proof.
unfold two_way_long_needle_low_level_spec_entail_high_level_spec; intros; Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_high_level_spec); Intros.
  assert (Hnonempty : needle0_high_level_spec <> nil).
  { intro E; subst needle0_high_level_spec; rewrite Zlength_nil in *; lia. }
  pose proof (two_way_generic_prog_sound hay0_high_level_spec needle0_high_level_spec) as Hsound.
  Exists hay0_high_level_spec needle0_high_level_spec hn_high_level_spec nn_high_level_spec.
  Exists (MonadErr.nrm (two_way_generic_prog hay0_high_level_spec needle0_high_level_spec) tt).
  split_pure_spatial.
  - cancel (UCharArray.full haystack_pre hn_high_level_spec hay0_high_level_spec).
    cancel (UCharArray.full needle_pre needle_len_pre needle0_high_level_spec).
    cancel (tw_terminator haystack_pre hn_high_level_spec).
    Intros_r retval; apply derivable1_wand_sepcon_adjoint; Intros.
    Exists (uchar_ptr_option_repr haystack_pre retval (sizeof (UCHAR))).
    split_pure_spatial; [entailer! | split_pures; dump_pre_spatial; try reflexivity].
    match goal with Hret : safeExec ATrue _ _ |- _ =>
      pose proof (Hoare_safeexec_compose _ _ _ Hsound _ _ _ Hret Hnonempty)
        as [st [Hpost _]]; exact Hpost
    end.
  - split_pures; dump_pre_spatial; auto.
    apply safeExec_monad_Atrue_finnal.
    exact (proj2 Hsound tt Hnonempty).
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_low_level_spec_entail_bind_spec : critical_factorization_low_level_spec_entail_bind_spec.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_low_level_spec_entail_bind_spec.
all: try entailer!.
Qed.

Lemma proof_of_critical_factorization_low_level_spec_entail_long_needle_bind_spec : critical_factorization_low_level_spec_entail_long_needle_bind_spec.
Proof.
exact two_way_rel_proof_manual.proof_of_critical_factorization_low_level_spec_entail_long_needle_bind_spec.
all: try entailer!.
Qed.

