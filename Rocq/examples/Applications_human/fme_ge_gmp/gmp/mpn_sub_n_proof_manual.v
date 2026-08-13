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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_sub_n_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_sub_n_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_sub_n_entail_wit_1_rp_eq_bp_split_goal_1 :
  mpn_sub_n_entail_wit_1_rp_eq_bp_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1_rp_eq_bp_split_goal_2 :
  mpn_sub_n_entail_wit_1_rp_eq_bp_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1_rp_eq_bp_split_goal_3 :
  mpn_sub_n_entail_wit_1_rp_eq_bp_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1_rp_eq_bp : mpn_sub_n_entail_wit_1_rp_eq_bp.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_n_entail_wit_1_rp_eq_bp_split_goal_1.
  Goal_apply proof_of_mpn_sub_n_entail_wit_1_rp_eq_bp_split_goal_2.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_rp_eq_ap_split_goal_1 :
  mpn_sub_n_entail_wit_2_rp_eq_ap_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_rp_eq_ap_split_goal_2 :
  mpn_sub_n_entail_wit_2_rp_eq_ap_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_rp_eq_ap_split_goal_3 :
  mpn_sub_n_entail_wit_2_rp_eq_ap_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_rp_eq_ap : mpn_sub_n_entail_wit_2_rp_eq_ap.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_n_entail_wit_2_rp_eq_ap_split_goal_1.
  Goal_apply proof_of_mpn_sub_n_entail_wit_2_rp_eq_ap_split_goal_2.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_3_1_rp_eq_bp : mpn_sub_n_entail_wit_3_1_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hbp_cy_no_overflow: Znth i l_b 0 + cy < UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *. apply ulb_ge_cy_implies_no_overflow; lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { unfold unsigned_last_nbits, UINT_MOD in *. rewrite Z.mod_small; lia. }
  set (out := Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. rewrite Hulb_eq. unfold UINT_MOD in *. lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg bp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg bp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
      rewrite (sublist_single 0 i l_a); try lia.
      rewrite list_to_Z_concat; try lia; try tauto.
      rewrite PreH11.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist; try lia.
      replace (i - 0) with i by lia. unfold UINT_MOD. ring.
      all: try (apply list_within_bound_sublist; try lia; try tauto).
      all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr. ring.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_3_2_rp_eq_bp : mpn_sub_n_entail_wit_3_2_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hbp_cy_no_overflow: Znth i l_b 0 + cy < UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *. apply ulb_ge_cy_implies_no_overflow; lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { unfold unsigned_last_nbits, UINT_MOD in *. rewrite Z.mod_small; lia. }
  set (out := unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. split; [| tauto].
    unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound; lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg bp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg bp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_a); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH11.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr.
    assert (Hdiff_neg: Znth i l_a 0 - (Znth i l_b 0 + cy) < 0) by lia.
    assert (Hdiff_bound: -4294967296 < Znth i l_a 0 - (Znth i l_b 0 + cy)) by lia.
    assert (Hmod_eq:
      (Znth i l_a 0 - (Znth i l_b 0 + cy)) mod 2 ^ 32 =
      Znth i l_a 0 - (Znth i l_b 0 + cy) + 4294967296).
    { symmetry. apply Z.mod_unique with (-1); [left; lia | ring]. }
    unfold unsigned_last_nbits.
    try rewrite Hmod_eq.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_3_3_rp_eq_bp : mpn_sub_n_entail_wit_3_3_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hoverflow: Znth i l_b 0 + cy >= UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    destruct (Z_lt_dec (Znth i l_b 0 + cy) (2^32)).
    - exfalso.
      assert (Hulb_small: (Znth i l_b 0 + cy) mod 2^32 = Znth i l_b 0 + cy).
      { apply Z.mod_small; lia. }
      lia.
    - lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy - UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_eq by lia.
    replace ((Znth i l_b 0 + cy) / 2^32) with 1.
    { ring. }
    apply Z.div_unique with (Znth i l_b 0 + cy - 2^32); lia. }
  set (out := Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. rewrite Hulb_eq. unfold UINT_MOD in *. lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg bp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg bp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_a); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH11.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_3_4_rp_eq_bp : mpn_sub_n_entail_wit_3_4_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hoverflow: Znth i l_b 0 + cy >= UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    destruct (Z_lt_dec (Znth i l_b 0 + cy) (2^32)).
    - exfalso.
      assert (Hulb_small: (Znth i l_b 0 + cy) mod 2^32 = Znth i l_b 0 + cy).
      { apply Z.mod_small; lia. }
      lia.
    - lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy - UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_eq by lia.
    replace ((Znth i l_b 0 + cy) / 2^32) with 1.
    { ring. }
    apply Z.div_unique with (Znth i l_b 0 + cy - 2^32); lia. }
  set (out := unsigned_last_nbits
    (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i)
    (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. split; [| tauto].
    unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound; lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg bp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg bp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_a); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH11.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr.
    assert (Hdiff_neg:
      Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296) < 0) by lia.
    assert (Hdiff_bound:
      -4294967296 < Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296)) by lia.
    assert (Hmod_eq:
      (Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296)) mod 2 ^ 32 =
      Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296) + 4294967296).
    { symmetry. apply Z.mod_unique with (-1); [left; lia | ring]. }
    unfold unsigned_last_nbits.
    try rewrite Hmod_eq.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_4_1_rp_eq_ap : mpn_sub_n_entail_wit_4_1_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Ha_sub: Znth (i - i) (sublist i (Zlength l_a) l_a) 0 = Znth i l_a 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Ha_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hbp_cy_no_overflow: Znth i l_b 0 + cy < UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *. apply ulb_ge_cy_implies_no_overflow; lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { unfold unsigned_last_nbits, UINT_MOD in *. rewrite Z.mod_small; lia. }
  set (out := Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. rewrite Hulb_eq. unfold UINT_MOD in *. lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_a) =
    out :: sublist (i + 1) (Zlength l_a) l_a).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg ap_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_a)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_a)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg ap_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_a); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH11.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr. ring.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_4_2_rp_eq_ap : mpn_sub_n_entail_wit_4_2_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Ha_sub: Znth (i - i) (sublist i (Zlength l_a) l_a) 0 = Znth i l_a 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Ha_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hbp_cy_no_overflow: Znth i l_b 0 + cy < UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *. apply ulb_ge_cy_implies_no_overflow; lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { unfold unsigned_last_nbits, UINT_MOD in *. rewrite Z.mod_small; lia. }
  set (out := unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. split; [| tauto].
    unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound; lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_a) =
    out :: sublist (i + 1) (Zlength l_a) l_a).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg ap_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_a)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_a)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg ap_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_a); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH11.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr.
    assert (Hdiff_neg: Znth i l_a 0 - (Znth i l_b 0 + cy) < 0) by lia.
    assert (Hdiff_bound: -4294967296 < Znth i l_a 0 - (Znth i l_b 0 + cy)) by lia.
    assert (Hmod_eq:
      (Znth i l_a 0 - (Znth i l_b 0 + cy)) mod 2 ^ 32 =
      Znth i l_a 0 - (Znth i l_b 0 + cy) + 4294967296).
    { symmetry. apply Z.mod_unique with (-1); [left; lia | ring]. }
    unfold unsigned_last_nbits.
    try rewrite Hmod_eq.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_4_3_rp_eq_ap : mpn_sub_n_entail_wit_4_3_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Ha_sub: Znth (i - i) (sublist i (Zlength l_a) l_a) 0 = Znth i l_a 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Ha_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hoverflow: Znth i l_b 0 + cy >= UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    destruct (Z_lt_dec (Znth i l_b 0 + cy) (2^32)).
    - exfalso.
      assert (Hulb_small: (Znth i l_b 0 + cy) mod 2^32 = Znth i l_b 0 + cy).
      { apply Z.mod_small; lia. }
      lia.
    - lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy - UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_eq by lia.
    replace ((Znth i l_b 0 + cy) / 2^32) with 1.
    { ring. }
    apply Z.div_unique with (Znth i l_b 0 + cy - 2^32); lia. }
  set (out := Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. rewrite Hulb_eq. unfold UINT_MOD in *. lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_a) =
    out :: sublist (i + 1) (Zlength l_a) l_a).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg ap_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_a)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_a)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg ap_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_a); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH11.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_4_4_rp_eq_ap : mpn_sub_n_entail_wit_4_4_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Ha_sub: Znth (i - i) (sublist i (Zlength l_a) l_a) 0 = Znth i l_a 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Ha_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hoverflow: Znth i l_b 0 + cy >= UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    destruct (Z_lt_dec (Znth i l_b 0 + cy) (2^32)).
    - exfalso.
      assert (Hulb_small: (Znth i l_b 0 + cy) mod 2^32 = Znth i l_b 0 + cy).
      { apply Z.mod_small; lia. }
      lia.
    - lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy - UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_eq by lia.
    replace ((Znth i l_b 0 + cy) / 2^32) with 1.
    { ring. }
    apply Z.div_unique with (Znth i l_b 0 + cy - 2^32); lia. }
  set (out := unsigned_last_nbits
    (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i)
    (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. split; [| tauto].
    unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound; lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_a) =
    out :: sublist (i + 1) (Zlength l_a) l_a).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg ap_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_a)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_a)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg ap_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_a); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH11.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr.
    assert (Hdiff_neg:
      Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296) < 0) by lia.
    assert (Hdiff_bound:
      -4294967296 < Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296)) by lia.
    assert (Hmod_eq:
      (Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296)) mod 2 ^ 32 =
      Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296) + 4294967296).
    { symmetry. apply Z.mod_unique with (-1); [left; lia | ring]. }
    unfold unsigned_last_nbits.
    try rewrite Hmod_eq.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.

Lemma proof_of_mpn_sub_n_return_wit_1_rp_eq_bp : mpn_sub_n_return_wit_1_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (i = n_pre) by lia.
  subst i.
  assert (Hrlen: Zlength l_r = n_pre) by lia.
  assert (Hval:
    val_r_2 - cy * UINT_MOD ^ n_pre =
    val_a_rp_eq_bp - val_b_rp_eq_bp).
  {
    rewrite Hrlen in PreH18.
    rewrite Hrlen in PreH9, PreH10.
    rewrite (sublist_self l_a n_pre) in PreH9 by lia.
    rewrite (sublist_self l_b n_pre) in PreH10 by lia.
    rewrite PreH23 in PreH9.
    rewrite PreH24 in PreH10.
    lia.
  }
  unfold mpd_store_Z, mpd_store_list.
  Exists val_r_2.
  rewrite Zsublist_nil by lia.
  replace (Zlength l_r) with n_pre by lia.
  replace (Zlength l_a) with n_pre by lia.
  sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 n_pre n_pre l_r (@nil Z)).
  rewrite app_nil_r.
  sep_apply (UIntArray.seg_to_full rp_pre 0 n_pre l_r).
  2: lia.
  replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  Exists l_a l_r.
  replace (Zlength l_r) with n_pre by lia.
  replace (Zlength l_a) with n_pre by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
    + split; assumption.
    + split; assumption.
Qed.

Lemma proof_of_mpn_sub_n_return_wit_2_rp_eq_ap : mpn_sub_n_return_wit_2_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (i = n_pre) by lia.
  subst i.
  assert (Hrlen: Zlength l_r = n_pre) by lia.
  assert (Hval:
    val_r_2 - cy * UINT_MOD ^ n_pre =
    val_a_rp_eq_ap - val_b_rp_eq_ap).
  {
    rewrite Hrlen in PreH18.
    rewrite Hrlen in PreH9, PreH10.
    rewrite (sublist_self l_a n_pre) in PreH9 by lia.
    rewrite (sublist_self l_b n_pre) in PreH10 by lia.
    rewrite PreH23 in PreH9.
    rewrite PreH24 in PreH10.
    lia.
  }
  unfold mpd_store_Z, mpd_store_list.
  Exists val_r_2.
  rewrite Zsublist_nil by lia.
  replace (Zlength l_r) with n_pre by lia.
  replace (Zlength l_a) with n_pre by lia.
  sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 n_pre n_pre l_r (@nil Z)).
  rewrite app_nil_r.
  sep_apply (UIntArray.seg_to_full rp_pre 0 n_pre l_r).
  2: lia.
  replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  Exists l_r l_b.
  replace (Zlength l_r) with n_pre by lia.
  replace (Zlength l_b) with n_pre by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
    + split; assumption.
    + split; assumption.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_1 : mpn_sub_n_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  rewrite <- H0, <- H2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_2 : mpn_sub_n_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  rewrite <- H0, <- H2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_3_split_goal_spatial :
  mpn_sub_n_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (UIntArray.full_Zlength ap n l_a).
  Intros.
  sep_apply_l_atomic (UIntArray.full_split_to_seg ap 0 n l_a).
  - dump_pre_spatial; lia.
  - rewrite Zsublist_nil by lia.
    replace n with (Zlength l_a) by lia.
    rewrite (sublist_self l_a (Zlength l_a)) by lia.
    rewrite UIntArray.seg_empty.
    Intros.
    cancel.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_3 : mpn_sub_n_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_n_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_4_split_goal_spatial :
  mpn_sub_n_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (UIntArray.full_Zlength bp n l_b).
  Intros.
  sep_apply_l_atomic (UIntArray.full_split_to_seg bp 0 n l_b).
  - dump_pre_spatial; lia.
  - rewrite Zsublist_nil by lia.
    replace n with (Zlength l_a) by lia.
    rewrite (sublist_self l_b (Zlength l_a)) by lia.
    rewrite UIntArray.seg_empty.
    Intros.
    cancel.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_4 : mpn_sub_n_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_n_which_implies_wit_4_split_goal_spatial.
Qed.
