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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_make_odd_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_make_odd_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_common_scan_safety_wit_3_split_goal_1 : mpn_common_scan_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [_ [Hpos Hcase]]]].
  destruct Hcase as [[Heq Hnz] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst. exfalso. lia.
  - LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_common_scan_safety_wit_3_split_goal_2 : mpn_common_scan_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [[Hi_nonneg Hi_pos] _]]].
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_common_scan_safety_wit_3 : mpn_common_scan_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_common_scan_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_mpn_common_scan_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_mpn_common_scan_safety_wit_4_split_goal_1 : mpn_common_scan_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [_ [Hpos Hcase]]]].
  destruct Hcase as [[Heq Hnz] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst. exfalso. lia.
  - LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_common_scan_safety_wit_4_split_goal_2 : mpn_common_scan_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [[Hi_nonneg Hi_pos] _]]].
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_common_scan_safety_wit_4 : mpn_common_scan_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_common_scan_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_mpn_common_scan_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_1_split_goal_1 : mpn_common_scan_entail_wit_2_1_split_goal_1.
Proof.
  unfold mpn_common_scan_entail_wit_2_1_split_goal_1.
  intros.
  replace ((i_pre + 1) - 1) with i_pre by lia.
  rewrite <- PreH1.
  exact PreH7.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_1_split_goal_2 : mpn_common_scan_entail_wit_2_1_split_goal_2.
Proof.
  unfold mpn_common_scan_entail_wit_2_1_split_goal_2.
  intros.
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [_ [Hpos Hcase]]]].
  destruct Hcase as [[Heq Hnz] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst. exfalso. lia.
  - lia.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_1_split_goal_3 : mpn_common_scan_entail_wit_2_1_split_goal_3.
Proof.
  unfold mpn_common_scan_entail_wit_2_1_split_goal_3.
  intros.
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [[Hi_nonneg Hi_pos] _]]].
  lia.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_1_split_goal_4 : mpn_common_scan_entail_wit_2_1_split_goal_4.
Proof.
  unfold mpn_common_scan_entail_wit_2_1_split_goal_4.
  intros.
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [_ [_ Hcase]]]].
  destruct Hcase as [[Heq Hnz] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst. exfalso. lia.
  - apply Hneq_un. lia.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_1 : mpn_common_scan_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_common_scan_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_mpn_common_scan_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_mpn_common_scan_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_mpn_common_scan_entail_wit_2_1_split_goal_4.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_2_split_goal_1 : mpn_common_scan_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace ((i + 1) - 1) with i by lia.
  rewrite <- PreH1.
  exact PreH7.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_2_split_goal_2 : mpn_common_scan_entail_wit_2_2_split_goal_2.
Proof.
  unfold mpn_common_scan_entail_wit_2_2_split_goal_2.
  intros.
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [_ [Hpos Hcase]]]].
  destruct Hcase as [[Heq Hnz] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst. exfalso. lia.
  - lia.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_2_split_goal_3 : mpn_common_scan_entail_wit_2_2_split_goal_3.
Proof.
  unfold mpn_common_scan_entail_wit_2_2_split_goal_3.
  intros.
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [[Hi_nonneg Hi_pos] _]]].
  lia.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_2_split_goal_4 : mpn_common_scan_entail_wit_2_2_split_goal_4.
Proof.
  unfold mpn_common_scan_entail_wit_2_2_split_goal_4.
  intros.
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [_ [_ Hcase]]]].
  destruct Hcase as [[Heq Hnz] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst. exfalso. lia.
  - apply Hneq_un. lia.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_2 : mpn_common_scan_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_common_scan_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_mpn_common_scan_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_mpn_common_scan_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_mpn_common_scan_entail_wit_2_2_split_goal_4.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_3_split_goal_1 : mpn_common_scan_entail_wit_3_split_goal_1.
Proof.
  unfold mpn_common_scan_entail_wit_3_split_goal_1.
  intros.
  unfold gmp_scan_limb.
  reflexivity.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_3_split_goal_2 : mpn_common_scan_entail_wit_3_split_goal_2.
Proof.
  unfold mpn_common_scan_entail_wit_3_split_goal_2.
  intros.
  unfold mpn_common_scan_target in PreH12 |- *.
  destruct PreH12 as
      [Hux [Hlimb_bound [Hi_prev [Hpos_bound Hscan]]]].
  pose proof
    (list_within_bound_Znth_bound UINT_MOD l_found i ltac:(lia) PreH10)
    as Hnth.
  assert (Hnth_uint : 0 <= Znth i l_found 0 <= 4294967295).
  {
    unfold UINT_MOD in Hnth.
    lia.
  }
  assert (Hxor : 0 <= Z.lxor ux_pre (Znth i l_found 0) <= 4294967295).
  {
    assert (Hux_copy := Hux).
    destruct Hux_copy as [Hux_zero | Hux_max].
    - rewrite Hux_zero, Z.lxor_0_l.
      exact Hnth_uint.
    - rewrite Hux_max, Z.lxor_comm.
      rewrite lxor_uintmax_sub by lia.
      lia.
  }
  destruct Hscan as [[Hpos_eq Hlimb_nonzero] |
                     [Hi_pos [Hlimb_zero [Hzero [Hun Hpos_nonzero]]]]].
  - exfalso.
    apply Hlimb_nonzero.
    exact PreH2.
  - split; [exact Hux |].
    split; [exact Hxor |].
    split; [lia |].
    split; [exact Hpos_bound |].
    destruct (Z.eq_dec i pos_found) as [Hi_eq | Hi_neq].
    + left.
      split; [symmetry; exact Hi_eq |].
      unfold gmp_scan_limb in Hpos_nonzero.
      rewrite Hi_eq.
      exact Hpos_nonzero.
    + right.
      repeat split.
      * lia.
      * unfold gmp_scan_limb in Hzero.
        apply Hzero.
        lia.
      * intros k Hk.
        apply Hzero.
        lia.
      * intros k Hk.
        apply Hun.
        lia.
      * exact Hpos_nonzero.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_3 : mpn_common_scan_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_common_scan_entail_wit_3_split_goal_1.
  Goal_apply proof_of_mpn_common_scan_entail_wit_3_split_goal_2.
Qed.

(* These split goals no longer exist in the generated goal interface.
Lemma proof_of_mpn_common_scan_entail_wit_5_1_split_goal_1 : mpn_common_scan_entail_wit_5_1_split_goal_1.
Proof.
  unfold mpn_common_scan_entail_wit_5_1_split_goal_1.
  intros.
  rewrite <- PreH5.
  exact PreH11.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_5_1_split_goal_2 : mpn_common_scan_entail_wit_5_1_split_goal_2.
Proof.
  unfold mpn_common_scan_entail_wit_5_1_split_goal_2.
  intros.
  rewrite <- PreH5.
  exact PreH12.
Qed.
*)

Lemma proof_of_mpn_common_scan_entail_wit_5_1 : mpn_common_scan_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists odd_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try solve [ rewrite <- PreH5; assumption | assumption | reflexivity | lia ].
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_5_2 : mpn_common_scan_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Right.
  Exists i_2 limb_2 odd_2.
  split_pure_spatial.
  - cancel ((( &( "limb" ) )) # UInt |-> limb_2).
    cancel ((( &( "i" ) )) # Int |-> i_2).
    cancel.
  - LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_common_scan_return_wit_1_split_goal_1 : mpn_common_scan_return_wit_1_split_goal_1.
Proof.
  intros ux_pre un_pre i_pre limb_pre pos_found n_found l_found odd cnt
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11.
  pose proof PreH10 as Htarget_bounds.
  unfold mpn_common_scan_target in Htarget_bounds.
  destruct Htarget_bounds as [_ [_ [Hi_bounds [Hpos_bound _]]]].
  assert (Hi64 : 0 <= i_pre < 2 ^ 64).
  { change (2 ^ 64) with 18446744073709551616. lia. }
  rewrite (unsigned_last_nbits_eq i_pre 64 Hi64).
  assert (Hmul64 : 0 <= i_pre * 32 < 2 ^ 64).
  { change (2 ^ 64) with 18446744073709551616. lia. }
  rewrite (unsigned_last_nbits_eq (i_pre * 32) 64 Hmul64).
  assert (Hsum64 : 0 <= i_pre * 32 + cnt < 2 ^ 64).
  { change (2 ^ 64) with 18446744073709551616. lia. }
  rewrite (unsigned_last_nbits_eq (i_pre * 32 + cnt) 64 Hsum64).
  unfold mpn_common_scan_result.
  split; [exact PreH10|].
  pose proof PreH11 as Hscan.
  unfold mpn_common_scan_target in Hscan.
  destruct Hscan as [_ [_ [_ [_ Hscan_case]]]].
  assert (Hpow_pos : 0 < 2 ^ cnt) by (apply Z.pow_pos_nonneg; lia).
  assert (Hlimb_pos : 0 < limb_pre) by (rewrite PreH5; nia).
  assert (Hpos_i : pos_found = i_pre).
  {
    destruct Hscan_case as [[Hpos_i _] | [_ [Hlimb_zero _]]].
    - exact Hpos_i.
    - lia.
  }
  exists cnt, odd.
  split; [lia|].
  split; [lia|].
  split; [exact PreH3|].
  split.
  { rewrite <- Z.rem_mod_nonneg by lia. exact PreH4. }
  left.
  split; [lia|exact PreH5].
Qed.

Lemma proof_of_mpn_common_scan_return_wit_1 : mpn_common_scan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_common_scan_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpn_common_scan_return_wit_2_split_goal_1 : mpn_common_scan_return_wit_2_split_goal_1.
Proof.
  intros ux_pre un_pre i_pre limb_pre pos_found n_found l_found odd cnt limb i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    PreH12 PreH13.
  pose proof PreH11 as Htarget_bounds.
  unfold mpn_common_scan_target in Htarget_bounds.
  destruct Htarget_bounds as [_ [_ [Hi_bounds [Hpos_bound _]]]].
  assert (Hi64 : 0 <= i < 2 ^ 64).
  { change (2 ^ 64) with 18446744073709551616. lia. }
  rewrite (unsigned_last_nbits_eq i 64 Hi64).
  assert (Hmul64 : 0 <= i * 32 < 2 ^ 64).
  { change (2 ^ 64) with 18446744073709551616. lia. }
  rewrite (unsigned_last_nbits_eq (i * 32) 64 Hmul64).
  assert (Hsum64 : 0 <= i * 32 + cnt < 2 ^ 64).
  { change (2 ^ 64) with 18446744073709551616. lia. }
  rewrite (unsigned_last_nbits_eq (i * 32 + cnt) 64 Hsum64).
  unfold mpn_common_scan_result.
  split; [exact PreH10|].
  pose proof PreH11 as Hscan.
  unfold mpn_common_scan_target in Hscan.
  destruct Hscan as [_ [_ [_ [_ Hscan_case]]]].
  assert (Hpow_pos : 0 < 2 ^ cnt) by (apply Z.pow_pos_nonneg; lia).
  assert (Hlimb_pos : 0 < limb) by (rewrite PreH5; nia).
  assert (Hpos_i : pos_found = i).
  {
    destruct Hscan_case as [[Hpos_i _] | [_ [Hlimb_zero _]]].
    - exact Hpos_i.
    - lia.
  }
  exists cnt, odd.
  split; [lia|].
  split; [lia|].
  split; [exact PreH3|].
  split.
  { rewrite <- Z.rem_mod_nonneg by lia. exact PreH4. }
  right.
  split; [lia|].
  subst pos_found.
  rewrite <- PreH13.
  exact PreH5.
Qed.

Lemma proof_of_mpn_common_scan_return_wit_2 : mpn_common_scan_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_common_scan_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpn_scan1_safety_wit_3_split_goal_1 : mpn_scan1_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hmod : 0 <= bit_pre % 32 < 32) by
    (apply Z.rem_bound_pos; lia).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpn_scan1_safety_wit_3_split_goal_2 : mpn_scan1_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hmod : 0 <= bit_pre % 32 < 32) by
    (apply Z.rem_bound_pos; lia).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpn_scan1_safety_wit_3 : mpn_scan1_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_scan1_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_mpn_scan1_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_mpn_scan1_entail_wit_1 : mpn_scan1_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpn_scan1_target in PreH7.
  destruct PreH7 as [Hbit_nonneg [pos Htarget]].
  assert (Hquot_div : bit_pre ÷ 32 = bit_pre / 32) by
    (apply Z.quot_div_nonneg; lia).
  assert (Hquot_nonneg : 0 <= bit_pre ÷ 32).
  {
    rewrite Hquot_div.
    apply Z.div_pos; lia.
  }
  assert (Hsigned :
            signed_last_nbits (bit_pre ÷ 32) 32 = bit_pre ÷ 32).
  {
    apply signed_last_nbits_eq; [lia|].
    change (-2147483648 <= bit_pre ÷ 32 < 2147483648).
    lia.
  }
  assert (Hrem_mod : bit_pre % 32 = bit_pre mod 32) by
    (apply Z.rem_mod_nonneg; lia).
  assert (Htarget' :
            mpn_common_scan_target l
              (Z.land (Znth (signed_last_nbits (bit_pre ÷ 32) 32) l 0)
                 (unsigned_last_nbits
                    (UINT_MAX * 2 ^ (bit_pre % 32)) 32))
              (signed_last_nbits (bit_pre ÷ 32) 32)
              (signed_last_nbits (bit_pre ÷ 32) 32) 0 pos).
  {
    rewrite Hsigned, Hquot_div, Hrem_mod.
    unfold gmp_scan1_limb, gmp_scan1_mask in Htarget.
    rewrite Z.shiftl_mul_pow2 in Htarget by
      (apply Z.mod_pos_bound; lia).
    exact Htarget.
  }
  Exists pos.
  split_pure_spatial.
  - cancel.
  - LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_scan1_return_wit_1_split_goal_1 : mpn_scan1_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpn_common_scan_result in PreH1.
  destruct PreH1 as
    [Htarget [cnt [odd [Hretval [Hcnt Hfound]]]]].
  unfold mpn_common_scan_target in Htarget.
  destruct Htarget as [_ [_ [_ [Hpos _]]]].
  subst retval.
  rewrite Z.quot_div_nonneg by nia.
  replace ((pos * 32 + cnt) / 32) with pos by
    (apply Z.div_unique with (r := cnt); lia).
  lia.
Qed.

Lemma proof_of_mpn_scan1_return_wit_1_split_goal_2 : mpn_scan1_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply scan1_common_result_implies_scan1_result; eauto.
Qed.

Lemma proof_of_mpn_scan1_return_wit_1 : mpn_scan1_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_scan1_return_wit_1_split_goal_1.
  - Goal_apply proof_of_mpn_scan1_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_mpn_scan1_partial_solve_wit_2_pure_split_goal_1 : mpn_scan1_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hrem : 0 <= bit_pre % 32 < 32) by
    (apply Z.rem_bound_pos; lia).
  dump_pre_spatial.
  rewrite Z.shiftl_mul_pow2 by lia.
  repeat rewrite <- PreH4.
  exact PreH12.
Qed.

Lemma proof_of_mpn_scan1_partial_solve_wit_2_pure_split_goal_2 : mpn_scan1_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hrem : 0 <= bit_pre % 32 < 32) by
    (apply Z.rem_bound_pos; lia).
  dump_pre_spatial.
  rewrite Z.shiftl_mul_pow2 by lia.
  repeat rewrite <- PreH4.
  exact PreH12.
Qed.

Lemma proof_of_mpn_scan1_partial_solve_wit_2_pure : mpn_scan1_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  sep_apply_l_atomic
    (proof_of_mpn_scan1_partial_solve_wit_2_pure_split_goal_1
       bit_pre ptr_pre n l i pos
       PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
       PreH7 PreH8 PreH9 PreH10 PreH11 PreH12).
  all: LLM_pre_process ltac:(int_auto);
    assert (Hrem : 0 <= bit_pre % 32 < 32) by
      (apply Z.rem_bound_pos; lia);
    rewrite Z.shiftl_mul_pow2 by lia;
    repeat rewrite <- PreH4;
    exact PreH12.
Qed.

Lemma proof_of_mpz_make_odd_entail_wit_1 : mpz_make_odd_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold store_Z at 1.
  Intros ptr size cap.
  unfold mpd_store_Z_compact, mpd_store_list at 1.
  Intros l.
  match goal with
  | H : list_to_Z UINT_MOD l = Z.abs z /\
        last l 1 >= 1 /\ list_within_bound UINT_MOD l |- _ =>
      destruct H as [Hval [Hlast Hbound]]
  end.
  match goal with
  | H : Z.abs size = Zlength l |- _ => rename H into Hlen_abs
  end.
  assert (Hval_z : list_to_Z UINT_MOD l = z).
  {
    rewrite Hval.
    apply Z.abs_eq.
    lia.
  }
  assert (Hlen_pos : Zlength l > 0).
  {
    pose proof (Zlength_nonneg l) as Hlen_nonneg.
    assert (Hlen_nonzero : Zlength l <> 0).
    {
      intro Hzero.
      apply Zlength_nil_inv in Hzero.
      subst l.
      rewrite list_to_Z_nil in Hval_z.
      lia.
    }
    lia.
  }
  assert (Hsize_nonneg : size >= 0).
  {
    match goal with
    | H : same_sign z size |- _ => unfold same_sign in H; lia
    end.
  }
  assert (Hlen : Zlength l = size).
  {
    rewrite <- Hlen_abs.
    rewrite Z.abs_eq by lia.
    reflexivity.
  }
  assert (Hsize_pos : size > 0) by lia.
  assert (Hscan : mpn_scan1_target l 0).
  {
    apply (mpn_scan1_target_0_of_positive l z); assumption.
  }
  Exists ptr l cap size.
  split_pure_spatial.
  - rewrite Hlen.
    rewrite Z.abs_eq by lia.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_make_odd_entail_wit_2_split_goal_1 : mpz_make_odd_entail_wit_2_split_goal_1.
Proof.
  intros z size cap l retval Hres.
  intros.
  unfold mpn_scan1_result in Hres.
  lia.
Qed.

Lemma proof_of_mpz_make_odd_entail_wit_2 : mpz_make_odd_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_make_odd_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpz_make_odd_entail_wit_3_split_goal_1 : mpz_make_odd_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_make_odd_entail_wit_3_split_goal_2 : mpz_make_odd_entail_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_make_odd_entail_wit_3_split_goal_3 : mpz_make_odd_entail_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_make_odd_entail_wit_3_split_goal_4 : mpz_make_odd_entail_wit_3_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_make_odd_entail_wit_3_split_goal_5 : mpz_make_odd_entail_wit_3_split_goal_5.
Proof. Abort.

Lemma proof_of_mpz_make_odd_entail_wit_3_split_goal_spatial : mpz_make_odd_entail_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_make_odd_entail_wit_3 : mpz_make_odd_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || idtac).
  Exists (Z.quot z (2 ^ shift)).
  split_pure_spatial.
  - assert (Hcompact : is_compact_Z UINT_MOD z size).
    { eapply is_compact_Z_from_full_last.
      - lia.
      - exact PreH7.
      - exact PreH9.
      - exact PreH8.
      - exact PreH10. }
    sep_apply_l_atomic
      (UIntArray_full_to_mpd_store_Z_compact
         ptr size l z PreH7 PreH8 PreH9 Hcompact).
    unfold store_Z.
    Exists ptr size cap.
    replace (Zabs z) with z by lia.
    replace (Zabs size) with size by lia.
    split_pure_spatial.
    + cancel (mpd_store_Z_compact UINT_MOD ptr z size).
      cancel (UIntArray.undef_seg ptr size cap).
      cancel.
    + LLM_pre_process ltac:(int_auto).
  - pose proof (mpn_scan1_result_make_odd
                  l z shift PreH1 PreH8 PreH12)
      as [Hfactor [Hodd Hpositive]].
    prop_apply
      (store_int_range
         (&(r_pre # "__mpz_struct" ->ₛ "_mp_size")) size).
    Intros.
    change Int.max_signed with 2147483647 in H.
    split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact Hpositive.
    + dump_pre_spatial.
      apply gmp_mod1_to_rem1; [lia | exact Hodd].
    + dump_pre_spatial. exact Hfactor.
Qed.
