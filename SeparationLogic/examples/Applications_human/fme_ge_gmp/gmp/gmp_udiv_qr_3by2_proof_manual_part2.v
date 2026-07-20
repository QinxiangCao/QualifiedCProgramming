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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qr_3by2_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qr_3by2_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.
Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_5_5 : gmp_udiv_qr_3by2_entail_wit_5_5.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_5_5; intros.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  set (qlo := unsigned_last_nbits (w0_value + n1_pre) 32) in *.
  set (qhat := unsigned_last_nbits (unsigned_last_nbits (w1_value + n2_pre) 32 + 1) 32) in *.
  set (rlo := unsigned_last_nbits (unsigned_last_nbits (n0_pre - d0_pre) 32 - w0_value_2) 32) in *.
  set (rhi := unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (n1_pre - unsigned_last_nbits (d1_pre * qhat) 32) 32 - d1_pre) 32 - 0) 32 - w1_value_2) 32 - 0) 32) in *.
  set (raw := n1_pre - d1_pre * qhat - d1_pre - 0 - w1_value_2 - 0 + n2_pre * 4294967296).
  assert (Hqlo_range: 0 <= qlo < 4294967296) by abstract lia.
  assert (Hqhat_range: 0 <= qhat <= 4294967295) by abstract lia.
  assert (Hrlo_range: 0 <= rlo <= 4294967295) by abstract
    (subst rlo;
     pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (n0_pre - d0_pre) 32 - w0_value_2) 32 ltac:(lia));
     change (2 ^ 32) with 4294967296 in *; lia).
  assert (Hrhi_range: 0 <= rhi <= 4294967295) by abstract
    (subst rhi;
     pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (n1_pre - unsigned_last_nbits (d1_pre * qhat) 32) 32 - d1_pre) 32 - 0) 32 - w1_value_2) 32 - 0) 32 ltac:(lia));
     change (2 ^ 32) with 4294967296 in *; lia).
  assert (Hcarry: w0_value + n1_pre = 1 * 4294967296 + qlo) by abstract
    (subst qlo; unfold unsigned_last_nbits; change (2 ^ 32) with 4294967296; eapply u32_add_carry_eq; eauto).
  assert (Hqhat_lt: w1_value + n2_pre + 1 < 4294967296) by abstract
    (pose proof (udiv_3by2_qhat_no_overflow d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo 1
      PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
      PreH23 PreH24 PreH20 PreH21 (proj1 Hqlo_range) (proj2 Hqlo_range) (or_intror eq_refl) Hcarry PreH33 PreH47 PreH48) as H; exact H).
  assert (Hqhat_eq: qhat = w1_value + n2_pre + 1) by abstract
    (subst qhat;
     assert (Hinner: unsigned_last_nbits (w1_value + n2_pre) 32 = w1_value + n2_pre) by abstract
       (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296; lia);
     rewrite Hinner; apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296; lia).
  assert (Hu0_eq: unsigned_last_nbits (n0_pre - d0_pre) 32 = n0_pre - d0_pre + 0 * 4294967296) by abstract
    (pose proof (u32_sub_no_borrow_eq n0_pre d0_pre PreH38 PreH39 PreH43 PreH44 PreH18) as Hnoborrow; rewrite Hnoborrow; ring).
  assert (Hrlo_eq: rlo = n0_pre - d0_pre + 0 * 4294967296 - w0_value_2 + 0 * 4294967296) by abstract
    (subst rlo; pose proof (u32_sub_no_borrow_eq (unsigned_last_nbits (n0_pre - d0_pre) 32) w0_value_2 ltac:(lia) PreH8 PreH5 PreH6 PreH1) as Hnoborrow; rewrite Hnoborrow, Hu0_eq; ring).
  assert (Hlo0: 0 <= n0_pre - d0_pre + 0 * 4294967296 < 4294967296) by abstract
    (rewrite <- Hu0_eq; lia).
  assert (Hlo1: 0 <= n0_pre - d0_pre + 0 * 4294967296 - w0_value_2 + 0 * 4294967296 < 4294967296) by abstract
    (rewrite <- Hrlo_eq; lia).
  assert (Hraw_range: qlo - 4294967296 <= raw < 4294967296) by abstract
    (subst raw;
     eapply (udiv_3by2_raw_high_between d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo qhat w0_value_2 w1_value_2 1 0 0);
     try exact PreH41; try exact PreH42; try exact PreH43; try exact PreH44; try exact PreH45; try exact PreH46;
     try exact PreH34; try exact PreH35; try exact PreH36; try exact PreH37; try exact PreH38; try exact PreH39; try exact PreH40;
     try exact PreH23; try exact PreH24; try exact PreH20; try exact PreH21;
     try exact (proj1 Hqlo_range); try exact (proj2 Hqlo_range); try exact PreH5; try exact PreH6; try exact PreH2; try exact PreH3;
     try (right; reflexivity); try (left; reflexivity); try exact Hcarry; try exact PreH33; try exact Hqhat_eq; try exact PreH17; try exact Hlo0; try exact Hlo1; try exact PreH47; try exact PreH48).
  assert (Hrhi_eq: rhi = unsigned_last_nbits raw 32) by abstract
    (subst rhi raw; rewrite (udiv_3by2_raw_high_expr_eq n1_pre d1_pre qhat 0 w1_value_2 0 n2_pre); reflexivity).
  pose proof (udiv_3by2_initial_split d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo qhat w0_value_2 w1_value_2 raw rlo rhi 1 0 0 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH23 PreH24 PreH20 PreH21 (proj1 Hqlo_range) (proj2 Hqlo_range) PreH5 PreH6 PreH2 PreH3 (or_intror eq_refl) (or_introl eq_refl) (or_introl eq_refl) Hcarry PreH33 Hqhat_eq PreH17 eq_refl Hrlo_eq Hrhi_eq (proj1 Hrlo_range) ltac:(lia) Hraw_range PreH47 PreH48) as Hsplit.
  destruct Hsplit as [[Hrlt Heq] | [[Hrge [Hover Heq]] | [Hrge [Hno Heq]]]].
  - Left; Left.
    Exists (qhat + 1).
    split_pure_spatial.
    2: {
      split_pures.
      all: dump_pre_spatial.
      all: first [reflexivity | exact Hrlt | exact Heq | lia].
    }
    cancel (q_pre # UInt |->_).
    cancel (r1_pre # UInt |->_).
    cancel (r0_pre # UInt |->_).
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    cancel (&( "t1") # UInt |->_).
    cancel (&( "t0") # UInt |->_).
    cancel (&( "x") # UInt |->_).
  - Left; Right.
    Exists (qhat + 1).
    split_pure_spatial.
    2: {
      split_pures.
      all: dump_pre_spatial.
      all: first [reflexivity | exact Hrge | exact Hover | exact Heq | lia].
    }
    cancel (q_pre # UInt |->_).
    cancel (r1_pre # UInt |->_).
    cancel (r0_pre # UInt |->_).
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    cancel (&( "t1") # UInt |->_).
    cancel (&( "t0") # UInt |->_).
    cancel (&( "x") # UInt |->_).
  - Right.
    Exists (qhat + 1).
    split_pure_spatial.
    2: {
      split_pures.
      all: dump_pre_spatial.
      all: first [reflexivity | exact Hrge | exact Hno | exact Heq | lia].
    }
    cancel (q_pre # UInt |->_).
    cancel (r1_pre # UInt |->_).
    cancel (r0_pre # UInt |->_).
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    cancel (&( "t1") # UInt |->_).
    cancel (&( "t0") # UInt |->_).
    cancel (&( "x") # UInt |->_).
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_5_6 : gmp_udiv_qr_3by2_entail_wit_5_6.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_5_6; intros.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  set (qlo := unsigned_last_nbits (w0_value + n1_pre) 32) in *.
  set (qhat := unsigned_last_nbits (unsigned_last_nbits (w1_value + n2_pre) 32 + 1) 32) in *.
  set (rlo := unsigned_last_nbits (unsigned_last_nbits (n0_pre - d0_pre) 32 - w0_value_2) 32) in *.
  set (rhi := unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (n1_pre - unsigned_last_nbits (d1_pre * qhat) 32) 32 - d1_pre) 32 - 0) 32 - w1_value_2) 32 - 1) 32) in *.
  set (raw := n1_pre - d1_pre * qhat - d1_pre - 0 - w1_value_2 - 1 + n2_pre * 4294967296).
  assert (Hqlo_range: 0 <= qlo < 4294967296) by abstract lia.
  assert (Hqhat_range: 0 <= qhat <= 4294967295) by abstract lia.
  assert (Hrlo_range: 0 <= rlo <= 4294967295) by abstract
    (subst rlo;
     pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (n0_pre - d0_pre) 32 - w0_value_2) 32 ltac:(lia));
     change (2 ^ 32) with 4294967296 in *; lia).
  assert (Hrhi_range: 0 <= rhi <= 4294967295) by abstract
    (subst rhi;
     pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (n1_pre - unsigned_last_nbits (d1_pre * qhat) 32) 32 - d1_pre) 32 - 0) 32 - w1_value_2) 32 - 1) 32 ltac:(lia));
     change (2 ^ 32) with 4294967296 in *; lia).
  assert (Hcarry: w0_value + n1_pre = 1 * 4294967296 + qlo) by abstract
    (subst qlo; unfold unsigned_last_nbits; change (2 ^ 32) with 4294967296; eapply u32_add_carry_eq; eauto).
  assert (Hqhat_lt: w1_value + n2_pre + 1 < 4294967296) by abstract
    (pose proof (udiv_3by2_qhat_no_overflow d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo 1
      PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
      PreH23 PreH24 PreH20 PreH21 (proj1 Hqlo_range) (proj2 Hqlo_range) (or_intror eq_refl) Hcarry PreH33 PreH47 PreH48) as H; exact H).
  assert (Hqhat_eq: qhat = w1_value + n2_pre + 1) by abstract
    (subst qhat;
     assert (Hinner: unsigned_last_nbits (w1_value + n2_pre) 32 = w1_value + n2_pre) by abstract
       (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296; lia);
     rewrite Hinner; apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296; lia).
  assert (Hu0_eq: unsigned_last_nbits (n0_pre - d0_pre) 32 = n0_pre - d0_pre + 0 * 4294967296) by abstract
    (pose proof (u32_sub_no_borrow_eq n0_pre d0_pre PreH38 PreH39 PreH43 PreH44 PreH18) as Hnoborrow; rewrite Hnoborrow; ring).
  assert (Hrlo_eq: rlo = n0_pre - d0_pre + 0 * 4294967296 - w0_value_2 + 1 * 4294967296) by abstract
    (subst rlo; pose proof (u32_sub_borrow_eq (unsigned_last_nbits (n0_pre - d0_pre) 32) w0_value_2 ltac:(lia) PreH8 PreH5 PreH6 PreH1) as Hborrow; rewrite Hborrow, Hu0_eq; ring).
  assert (Hlo0: 0 <= n0_pre - d0_pre + 0 * 4294967296 < 4294967296) by abstract
    (rewrite <- Hu0_eq; lia).
  assert (Hlo1: 0 <= n0_pre - d0_pre + 0 * 4294967296 - w0_value_2 + 1 * 4294967296 < 4294967296) by abstract
    (rewrite <- Hrlo_eq; lia).
  assert (Hraw_range: qlo - 4294967296 <= raw < 4294967296) by abstract
    (subst raw;
     eapply (udiv_3by2_raw_high_between d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo qhat w0_value_2 w1_value_2 1 0 1);
     try exact PreH41; try exact PreH42; try exact PreH43; try exact PreH44; try exact PreH45; try exact PreH46;
     try exact PreH34; try exact PreH35; try exact PreH36; try exact PreH37; try exact PreH38; try exact PreH39; try exact PreH40;
     try exact PreH23; try exact PreH24; try exact PreH20; try exact PreH21;
     try exact (proj1 Hqlo_range); try exact (proj2 Hqlo_range); try exact PreH5; try exact PreH6; try exact PreH2; try exact PreH3;
     try (right; reflexivity); try (left; reflexivity); try exact Hcarry; try exact PreH33; try exact Hqhat_eq; try exact PreH17; try exact Hlo0; try exact Hlo1; try exact PreH47; try exact PreH48).
  assert (Hrhi_eq: rhi = unsigned_last_nbits raw 32) by abstract
    (subst rhi raw; rewrite (udiv_3by2_raw_high_expr_eq n1_pre d1_pre qhat 0 w1_value_2 1 n2_pre); reflexivity).
  pose proof (udiv_3by2_initial_split d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo qhat w0_value_2 w1_value_2 raw rlo rhi 1 0 1 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH23 PreH24 PreH20 PreH21 (proj1 Hqlo_range) (proj2 Hqlo_range) PreH5 PreH6 PreH2 PreH3 (or_intror eq_refl) (or_introl eq_refl) (or_intror eq_refl) Hcarry PreH33 Hqhat_eq PreH17 eq_refl Hrlo_eq Hrhi_eq (proj1 Hrlo_range) ltac:(lia) Hraw_range PreH47 PreH48) as Hsplit.
  destruct Hsplit as [[Hrlt Heq] | [[Hrge [Hover Heq]] | [Hrge [Hno Heq]]]].
  - Left; Left.
    Exists (qhat + 1).
    split_pure_spatial.
    2: {
      split_pures.
      all: dump_pre_spatial.
      all: first [reflexivity | exact Hrlt | exact Heq | lia].
    }
    cancel (q_pre # UInt |->_).
    cancel (r1_pre # UInt |->_).
    cancel (r0_pre # UInt |->_).
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    cancel (&( "t1") # UInt |->_).
    cancel (&( "t0") # UInt |->_).
    cancel (&( "x") # UInt |->_).
  - Left; Right.
    Exists (qhat + 1).
    split_pure_spatial.
    2: {
      split_pures.
      all: dump_pre_spatial.
      all: first [reflexivity | exact Hrge | exact Hover | exact Heq | lia].
    }
    cancel (q_pre # UInt |->_).
    cancel (r1_pre # UInt |->_).
    cancel (r0_pre # UInt |->_).
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    cancel (&( "t1") # UInt |->_).
    cancel (&( "t0") # UInt |->_).
    cancel (&( "x") # UInt |->_).
  - Right.
    Exists (qhat + 1).
    split_pure_spatial.
    2: {
      split_pures.
      all: dump_pre_spatial.
      all: first [reflexivity | exact Hrge | exact Hno | exact Heq | lia].
    }
    cancel (q_pre # UInt |->_).
    cancel (r1_pre # UInt |->_).
    cancel (r0_pre # UInt |->_).
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    cancel (&( "t1") # UInt |->_).
    cancel (&( "t0") # UInt |->_).
    cancel (&( "x") # UInt |->_).
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_5_7 : gmp_udiv_qr_3by2_entail_wit_5_7.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_5_7; intros.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  set (qlo := unsigned_last_nbits (w0_value + n1_pre) 32) in *.
  set (qhat := unsigned_last_nbits (unsigned_last_nbits (w1_value + n2_pre) 32 + 1) 32) in *.
  set (rlo := unsigned_last_nbits (unsigned_last_nbits (n0_pre - d0_pre) 32 - w0_value_2) 32) in *.
  set (rhi := unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (n1_pre - unsigned_last_nbits (d1_pre * qhat) 32) 32 - d1_pre) 32 - 1) 32 - w1_value_2) 32 - 0) 32) in *.
  set (raw := n1_pre - d1_pre * qhat - d1_pre - 1 - w1_value_2 - 0 + n2_pre * 4294967296).
  assert (Hqlo_range: 0 <= qlo < 4294967296) by abstract lia.
  assert (Hqhat_range: 0 <= qhat <= 4294967295) by abstract lia.
  assert (Hrlo_range: 0 <= rlo <= 4294967295) by abstract
    (subst rlo;
     pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (n0_pre - d0_pre) 32 - w0_value_2) 32 ltac:(lia));
     change (2 ^ 32) with 4294967296 in *; lia).
  assert (Hrhi_range: 0 <= rhi <= 4294967295) by abstract
    (subst rhi;
     pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (n1_pre - unsigned_last_nbits (d1_pre * qhat) 32) 32 - d1_pre) 32 - 1) 32 - w1_value_2) 32 - 0) 32 ltac:(lia));
     change (2 ^ 32) with 4294967296 in *; lia).
  assert (Hcarry: w0_value + n1_pre = 1 * 4294967296 + qlo) by abstract
    (subst qlo; unfold unsigned_last_nbits; change (2 ^ 32) with 4294967296; eapply u32_add_carry_eq; eauto).
  assert (Hqhat_lt: w1_value + n2_pre + 1 < 4294967296) by abstract
    (pose proof (udiv_3by2_qhat_no_overflow d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo 1
      PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
      PreH23 PreH24 PreH20 PreH21 (proj1 Hqlo_range) (proj2 Hqlo_range) (or_intror eq_refl) Hcarry PreH33 PreH47 PreH48) as H; exact H).
  assert (Hqhat_eq: qhat = w1_value + n2_pre + 1) by abstract
    (subst qhat;
     assert (Hinner: unsigned_last_nbits (w1_value + n2_pre) 32 = w1_value + n2_pre) by abstract
       (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296; lia);
     rewrite Hinner; apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296; lia).
  assert (Hu0_eq: unsigned_last_nbits (n0_pre - d0_pre) 32 = n0_pre - d0_pre + 4294967296) by abstract
    (eapply u32_sub_borrow_eq; eauto).
  assert (Hrlo_eq: rlo = n0_pre - d0_pre + 1 * 4294967296 - w0_value_2 + 0 * 4294967296) by abstract
    (subst rlo; pose proof (u32_sub_no_borrow_eq (unsigned_last_nbits (n0_pre - d0_pre) 32) w0_value_2 ltac:(lia) PreH8 PreH5 PreH6 PreH1) as Hnoborrow; rewrite Hnoborrow, Hu0_eq; ring).
  assert (Hlo0: 0 <= n0_pre - d0_pre + 1 * 4294967296 < 4294967296) by abstract
    (replace (n0_pre - d0_pre + 1 * 4294967296) with (n0_pre - d0_pre + 4294967296) by ring; rewrite <- Hu0_eq; lia).
  assert (Hlo1: 0 <= n0_pre - d0_pre + 1 * 4294967296 - w0_value_2 + 0 * 4294967296 < 4294967296) by abstract
    (rewrite <- Hrlo_eq; lia).
  assert (Hraw_range: qlo - 4294967296 <= raw < 4294967296) by abstract
    (subst raw;
     eapply (udiv_3by2_raw_high_between d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo qhat w0_value_2 w1_value_2 1 1 0);
     try exact PreH41; try exact PreH42; try exact PreH43; try exact PreH44; try exact PreH45; try exact PreH46;
     try exact PreH34; try exact PreH35; try exact PreH36; try exact PreH37; try exact PreH38; try exact PreH39; try exact PreH40;
     try exact PreH23; try exact PreH24; try exact PreH20; try exact PreH21;
     try exact (proj1 Hqlo_range); try exact (proj2 Hqlo_range); try exact PreH5; try exact PreH6; try exact PreH2; try exact PreH3;
     try (right; reflexivity); try (left; reflexivity); try exact Hcarry; try exact PreH33; try exact Hqhat_eq; try exact PreH17; try exact Hlo0; try exact Hlo1; try exact PreH47; try exact PreH48).
  assert (Hrhi_eq: rhi = unsigned_last_nbits raw 32) by abstract
    (subst rhi raw; rewrite (udiv_3by2_raw_high_expr_eq n1_pre d1_pre qhat 1 w1_value_2 0 n2_pre); reflexivity).
  pose proof (udiv_3by2_initial_split d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo qhat w0_value_2 w1_value_2 raw rlo rhi 1 1 0 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH23 PreH24 PreH20 PreH21 (proj1 Hqlo_range) (proj2 Hqlo_range) PreH5 PreH6 PreH2 PreH3 (or_intror eq_refl) (or_intror eq_refl) (or_introl eq_refl) Hcarry PreH33 Hqhat_eq PreH17 eq_refl Hrlo_eq Hrhi_eq (proj1 Hrlo_range) ltac:(lia) Hraw_range PreH47 PreH48) as Hsplit.
  destruct Hsplit as [[Hrlt Heq] | [[Hrge [Hover Heq]] | [Hrge [Hno Heq]]]].
  - Left; Left.
    Exists (qhat + 1).
    split_pure_spatial.
    2: {
      split_pures.
      all: dump_pre_spatial.
      all: first [reflexivity | exact Hrlt | exact Heq | lia].
    }
    cancel (q_pre # UInt |->_).
    cancel (r1_pre # UInt |->_).
    cancel (r0_pre # UInt |->_).
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    cancel (&( "t1") # UInt |->_).
    cancel (&( "t0") # UInt |->_).
    cancel (&( "x") # UInt |->_).
  - Left; Right.
    Exists (qhat + 1).
    split_pure_spatial.
    2: {
      split_pures.
      all: dump_pre_spatial.
      all: first [reflexivity | exact Hrge | exact Hover | exact Heq | lia].
    }
    cancel (q_pre # UInt |->_).
    cancel (r1_pre # UInt |->_).
    cancel (r0_pre # UInt |->_).
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    cancel (&( "t1") # UInt |->_).
    cancel (&( "t0") # UInt |->_).
    cancel (&( "x") # UInt |->_).
  - Right.
    Exists (qhat + 1).
    split_pure_spatial.
    2: {
      split_pures.
      all: dump_pre_spatial.
      all: first [reflexivity | exact Hrge | exact Hno | exact Heq | lia].
    }
    cancel (q_pre # UInt |->_).
    cancel (r1_pre # UInt |->_).
    cancel (r0_pre # UInt |->_).
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    sep_apply_left store_uint_undef_store_uint.
    cancel (&( "t1") # UInt |->_).
    cancel (&( "t0") # UInt |->_).
    cancel (&( "x") # UInt |->_).
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_5_8 : gmp_udiv_qr_3by2_entail_wit_5_8.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_5_8; intros.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  set (qlo := unsigned_last_nbits (w0_value + n1_pre) 32) in *.
  set (qhat := unsigned_last_nbits (unsigned_last_nbits (w1_value + n2_pre) 32 + 1) 32) in *.
  set (rlo := unsigned_last_nbits (unsigned_last_nbits (n0_pre - d0_pre) 32 - w0_value_2) 32) in *.
  set (rhi := unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (n1_pre - unsigned_last_nbits (d1_pre * qhat) 32) 32 - d1_pre) 32 - 1) 32 - w1_value_2) 32 - 1) 32) in *.
  set (raw := n1_pre - d1_pre * qhat - d1_pre - 1 - w1_value_2 - 1 + n2_pre * 4294967296).
  assert (Hqlo_range: 0 <= qlo < 4294967296) by abstract lia.
  assert (Hqhat_range: 0 <= qhat <= 4294967295) by abstract lia.
  assert (Hrlo_range: 0 <= rlo <= 4294967295) by abstract
    (subst rlo;
     pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (n0_pre - d0_pre) 32 - w0_value_2) 32 ltac:(lia));
     change (2 ^ 32) with 4294967296 in *; lia).
  assert (Hrhi_range: 0 <= rhi <= 4294967295) by abstract
    (subst rhi;
     pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (unsigned_last_nbits (n1_pre - unsigned_last_nbits (d1_pre * qhat) 32) 32 - d1_pre) 32 - 1) 32 - w1_value_2) 32 - 1) 32 ltac:(lia));
     change (2 ^ 32) with 4294967296 in *; lia).
  assert (Hcarry: w0_value + n1_pre = 1 * 4294967296 + qlo) by abstract
    (subst qlo; unfold unsigned_last_nbits; change (2 ^ 32) with 4294967296; eapply u32_add_carry_eq; eauto).
  assert (Hqhat_lt: w1_value + n2_pre + 1 < 4294967296) by abstract
    (pose proof (udiv_3by2_qhat_no_overflow d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo 1
      PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
      PreH23 PreH24 PreH20 PreH21 (proj1 Hqlo_range) (proj2 Hqlo_range) (or_intror eq_refl) Hcarry PreH33 PreH47 PreH48) as H; exact H).
  assert (Hqhat_eq: qhat = w1_value + n2_pre + 1) by abstract
    (subst qhat;
     assert (Hinner: unsigned_last_nbits (w1_value + n2_pre) 32 = w1_value + n2_pre) by abstract
       (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296; lia);
     rewrite Hinner; apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296; lia).
  assert (Hu0_eq: unsigned_last_nbits (n0_pre - d0_pre) 32 = n0_pre - d0_pre + 4294967296) by abstract
    (eapply u32_sub_borrow_eq; eauto).
  assert (Hrlo_eq: rlo = n0_pre - d0_pre + 1 * 4294967296 - w0_value_2 + 1 * 4294967296) by abstract
    (subst rlo; pose proof (u32_sub_borrow_eq (unsigned_last_nbits (n0_pre - d0_pre) 32) w0_value_2 ltac:(lia) PreH8 PreH5 PreH6 PreH1) as Hborrow; rewrite Hborrow, Hu0_eq; ring).
  assert (Hlo0: 0 <= n0_pre - d0_pre + 1 * 4294967296 < 4294967296) by abstract
    (replace (n0_pre - d0_pre + 1 * 4294967296) with (n0_pre - d0_pre + 4294967296) by ring; rewrite <- Hu0_eq; lia).
  assert (Hlo1: 0 <= n0_pre - d0_pre + 1 * 4294967296 - w0_value_2 + 1 * 4294967296 < 4294967296) by abstract
    (rewrite <- Hrlo_eq; lia).
  assert (Hraw_range: qlo - 4294967296 <= raw < 4294967296) by abstract
    (subst raw;
     eapply (udiv_3by2_raw_high_between d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo qhat w0_value_2 w1_value_2 1 1 1);
     try exact PreH41; try exact PreH42; try exact PreH43; try exact PreH44; try exact PreH45; try exact PreH46;
     try exact PreH34; try exact PreH35; try exact PreH36; try exact PreH37; try exact PreH38; try exact PreH39; try exact PreH40;
     try exact PreH23; try exact PreH24; try exact PreH20; try exact PreH21;
     try exact (proj1 Hqlo_range); try exact (proj2 Hqlo_range); try exact PreH5; try exact PreH6; try exact PreH2; try exact PreH3;
     try (right; reflexivity); try exact Hcarry; try exact PreH33; try exact Hqhat_eq; try exact PreH17; try exact Hlo0; try exact Hlo1; try exact PreH47; try exact PreH48).
  assert (Hrhi_eq: rhi = unsigned_last_nbits raw 32) by abstract
    (subst rhi raw; rewrite (udiv_3by2_raw_high_expr_eq n1_pre d1_pre qhat 1 w1_value_2 1 n2_pre); reflexivity).
  pose proof (udiv_3by2_initial_split d1_pre d0_pre dinv_pre n2_pre n1_pre n0_pre w0_value w1_value qlo qhat w0_value_2 w1_value_2 raw rlo rhi 1 1 1 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH23 PreH24 PreH20 PreH21 (proj1 Hqlo_range) (proj2 Hqlo_range) PreH5 PreH6 PreH2 PreH3 (or_intror eq_refl) (or_intror eq_refl) (or_intror eq_refl) Hcarry PreH33 Hqhat_eq PreH17 eq_refl Hrlo_eq Hrhi_eq (proj1 Hrlo_range) ltac:(lia) Hraw_range PreH47 PreH48) as Hsplit.
  destruct Hsplit as [[Hrlt Heq] | [[Hrge [Hover Heq]] | [Hrge [Hno Heq]]]].
  - Left; Left.
    Exists (qhat + 1).
    split_pure_spatial.
    + cancel (q_pre # UInt |->_).
      cancel (r1_pre # UInt |->_).
      cancel (r0_pre # UInt |->_).
      sep_apply_left store_uint_undef_store_uint.
      sep_apply_left store_uint_undef_store_uint.
      sep_apply_left store_uint_undef_store_uint.
      cancel (&( "t1") # UInt |->_).
      cancel (&( "t0") # UInt |->_).
      cancel (&( "x") # UInt |->_).
    + split_pures; try solve [dump_pre_spatial; first [reflexivity | exact Hrlt | exact Heq | lia]].
  - Left; Right.
    Exists (qhat + 1).
    split_pure_spatial.
    + cancel (q_pre # UInt |->_).
      cancel (r1_pre # UInt |->_).
      cancel (r0_pre # UInt |->_).
      sep_apply_left store_uint_undef_store_uint.
      sep_apply_left store_uint_undef_store_uint.
      sep_apply_left store_uint_undef_store_uint.
      cancel (&( "t1") # UInt |->_).
      cancel (&( "t0") # UInt |->_).
      cancel (&( "x") # UInt |->_).
    + split_pures; try solve [dump_pre_spatial; first [reflexivity | exact Hrge | exact Hover | exact Heq | lia]].
  - Right.
    Exists (qhat + 1).
    split_pure_spatial.
    + cancel (q_pre # UInt |->_).
      cancel (r1_pre # UInt |->_).
      cancel (r0_pre # UInt |->_).
      sep_apply_left store_uint_undef_store_uint.
      sep_apply_left store_uint_undef_store_uint.
      sep_apply_left store_uint_undef_store_uint.
      cancel (&( "t1") # UInt |->_).
      cancel (&( "t0") # UInt |->_).
      cancel (&( "x") # UInt |->_).
    + split_pures; try solve [dump_pre_spatial; first [reflexivity | exact Hrge | exact Hno | exact Heq | lia]].
Qed.
