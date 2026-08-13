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
From SimpleC.SL Require Import Mem SeparationLogic IntLib.
From SimpleC.EE.Applications_human.minigmp Require Import gmp_goal GmpMulAux.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minigmp Require Import GmpAux GmpNumber GmpMulAux.
Import Aux.
Local Open Scope sac.

(* ============================================================
   第一部分：位运算辅助引理
   ============================================================ *)

Lemma proof_of_gmp_umul_ppmm_return_wit_1_split_goal_1 :
  gmp_umul_ppmm_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  (* 证明数学等式：w1_value * UINT_MOD + w0_value = u_pre * v_pre *)
  (* 使用GmpAux.v中的umul_ppmm_correct_with_carry引理 *)
  unfold UINT_MOD.
  
  (* 定义算法中的各个部分 *)
  set (ul := Z.land u_pre 65535).
  set (uh := Z.shiftr u_pre 16).
  set (vl := Z.land v_pre 65535).
  set (vh := Z.shiftr v_pre 16).
  set (x0 := ul * vl).
  set (x1 := ul * vh).
  set (x2 := uh * vl).
  set (x3 := uh * vh).
  set (x1' := (x1 + Z.shiftr x0 16) mod 4294967296).
  set (x1'' := (x1' + x2) mod 4294967296).
  
  (* 定义w1和w0根据引理 *)
  set (w1 := ((x3 + 65536) mod 4294967296 + Z.shiftr x1'' 16) mod 4294967296).
  set (w0 := ((Z.shiftl x1'' 16) mod 4294967296 + Z.land x0 65535) mod 4294967296).
  assert (Hu32: 0 <= u_pre < 4294967296) by lia.
  assert (Hv32: 0 <= v_pre < 4294967296) by lia.
  
  (* 使用umul_ppmm_correct_with_carry引理证明w1 * 4294967296 + w0 = u_pre * v_pre *)
  pose proof (umul_ppmm_correct_with_carry u_pre v_pre ul uh vl vh x0 x1 x2 x3
    Hu32
    Hv32
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as Hlemma.
  
  assert (Hcarry: x1'' < x2). {
    assert (Hx1pp_bounds: 0 <= x1'' < 4294967296).
    { unfold x1'', x1'. apply Z.mod_pos_bound. lia. }
    assert (Hx2_bounds: 0 <= x2 < 4294967296).
    { unfold x2, uh, vl.
      pose proof (shiftr_16_full_bounds u_pre Hu32) as Huh.
      pose proof (land_65535_bounds_alt v_pre) as Hvl.
      split.
      + apply Z.mul_nonneg_nonneg; lia.
      + assert (Z.shiftr u_pre 16 * Z.land v_pre 65535 < 65536 * 65536) by nia.
        lia. }
    assert (Hcarry_bits: unsigned_last_nbits x1'' 32 < unsigned_last_nbits x2 32).
    { unfold x1'', x1', x0, x1, x2, ul, uh, vl, vh.
      apply (carry_condition_transform u_pre v_pre); [exact Hu32 | exact Hv32 | exact PreH1].
    }
    rewrite (unsigned_last_nbits_eq x1'' 32) in Hcarry_bits by lia.
    rewrite (unsigned_last_nbits_eq x2 32) in Hcarry_bits by lia.
    exact Hcarry_bits.
  }
  
  (* 应用引理获得结论 *)
  specialize (Hlemma Hcarry).
  
  (* 展开 let 绑定 *)
  unfold w1, w0 in Hlemma.
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul in Hlemma.
  
  (* 转换目标中的 unsigned_last_nbits 为 mod 形式 *)
  repeat (unfold unsigned_last_nbits; change (2 ^ 32) with 4294967296).
  
  (* 展开目标中的变量定义 *)
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul.
  
  (* 使用VC前提中的局部range事实获取边界 *)
  pose proof Hu32 as Hu.
  pose proof Hv32 as Hv.
  
  
  (* 证明各部分在范围内 *)
  assert (Hul_bounds: 0 <= Z.land u_pre 65535 < 65536) by (apply land_65535_bounds_alt).
  assert (Hvl_bounds: 0 <= Z.land v_pre 65535 < 65536) by (apply land_65535_bounds_alt).
  assert (Huh_bounds: 0 <= Z.shiftr u_pre 16 < 65536) by (apply shiftr_16_full_bounds; exact Hu).
  assert (Hvh_bounds: 0 <= Z.shiftr v_pre 16 < 65536) by (apply shiftr_16_full_bounds; exact Hv).
  
  (* 各乘积在 [0, 2^32) 范围内 *)
  assert (Hx0_small: 0 <= Z.land u_pre 65535 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx1_small: 0 <= Z.land u_pre 65535 * Z.shiftr v_pre 16 < 4294967296) by nia.
  assert (Hx2_small: 0 <= Z.shiftr u_pre 16 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx3_small: 0 <= Z.shiftr u_pre 16 * Z.shiftr v_pre 16 < 4294967296) by nia.
  
  (* 简化 mod 操作 *)
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.shiftr v_pre 16) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.shiftr v_pre 16) 4294967296) by lia.
  
  exact Hlemma.
Qed.

Lemma proof_of_gmp_umul_ppmm_return_wit_1 : gmp_umul_ppmm_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_umul_ppmm_return_wit_1_split_goal_1.
Qed.

(* ============================================================
   第七部分：mpn_mul_1 正确性证明
   
   算法：多精度数乘以单精度数
   输入：n位数组up，单精度数vl
   输出：n位数组rp，返回进位cl
   证明目标：rp表示的数 + cl * 2^(32n) = up表示的数 * vl
   ============================================================ *)

(* 循环入口：初始化空结果列表 *)

Lemma proof_of_gmp_umul_ppmm_return_wit_2_split_goal_1 :
  gmp_umul_ppmm_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  (* 证明数学等式：w1_value * UINT_MOD + w0_value = u_pre * v_pre *)
  (* 使用GmpAux.v中的umul_ppmm_correct_no_carry引理 *)
  unfold UINT_MOD.
  
  (* 定义算法中的各个部分 *)
  set (ul := Z.land u_pre 65535).
  set (uh := Z.shiftr u_pre 16).
  set (vl := Z.land v_pre 65535).
  set (vh := Z.shiftr v_pre 16).
  set (x0 := ul * vl).
  set (x1 := ul * vh).
  set (x2 := uh * vl).
  set (x3 := uh * vh).
  set (x1' := (x1 + Z.shiftr x0 16) mod 4294967296).
  set (x1'' := (x1' + x2) mod 4294967296).
  
  (* 定义w1和w0根据引理（无进位情况） *)
  set (w1 := (x3 + Z.shiftr x1'' 16) mod 4294967296).
  set (w0 := ((Z.shiftl x1'' 16) mod 4294967296 + Z.land x0 65535) mod 4294967296).
  assert (Hu32: 0 <= u_pre < 4294967296) by lia.
  assert (Hv32: 0 <= v_pre < 4294967296) by lia.
  
  (* 使用umul_ppmm_correct_no_carry引理 *)
  pose proof (umul_ppmm_correct_no_carry u_pre v_pre ul uh vl vh x0 x1 x2 x3
    Hu32
    Hv32
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as Hlemma.
  
  assert (Hnocarry: x1'' >= x2). {
    pose proof Hu32 as Hu.
    pose proof Hv32 as Hv.
    

    assert (Hx1_exp: 0 <= Z.land u_pre 65535 * Z.shiftr v_pre 16 < 4294967296).
    { pose proof (land_65535_bounds_alt u_pre) as Hul.
      pose proof (shiftr_16_full_bounds v_pre Hv) as Hvh.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }
    assert (Hx0_exp: 0 <= Z.land u_pre 65535 * Z.land v_pre 65535 < 4294967296).
    { pose proof (land_65535_bounds_alt u_pre) as Hul.
      pose proof (land_65535_bounds_alt v_pre) as Hvl.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }
    assert (Hx2_exp: 0 <= Z.shiftr u_pre 16 * Z.land v_pre 65535 < 4294967296).
    { pose proof (shiftr_16_full_bounds u_pre Hu) as Huh.
      pose proof (land_65535_bounds_alt v_pre) as Hvl.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }

    rewrite (unsigned_last_nbits_eq (Z.land u_pre 65535 * Z.shiftr v_pre 16) 32) in PreH1 by lia.
    rewrite (unsigned_last_nbits_eq (Z.land u_pre 65535 * Z.land v_pre 65535) 32) in PreH1 by lia.
    rewrite (unsigned_last_nbits_eq (Z.shiftr u_pre 16 * Z.land v_pre 65535) 32) in PreH1 by lia.
    unfold unsigned_last_nbits in PreH1.
    change (2 ^ 32) with 4294967296 in PreH1.
    unfold x1'', x1', x0, x1, x2, ul, uh, vl, vh.
    exact PreH1.
  }
  
  (* 应用引理获得结论 *)
  specialize (Hlemma Hnocarry).
  
  (* 展开 let 绑定 *)
  unfold w1, w0 in Hlemma.
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul in Hlemma.
  
  (* 转换目标中的 unsigned_last_nbits 为 mod 形式 *)
  repeat (unfold unsigned_last_nbits; change (2 ^ 32) with 4294967296).
  
  (* 展开目标中的变量定义 *)
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul.
  
  (* 现在需要证明两个表达式相等，它们形式上略有不同 *)
  (* Hlemma 中：直接的乘法表达式 *)
  (* 目标中：带有额外 mod 的表达式 *)
  (* 由于 x0, x1, x2, x3 都在 [0, 2^32) 范围内，mod 4294967296 是恒等变换 *)
  
  (* 使用VC前提中的局部range事实获取边界 *)
  pose proof Hu32 as Hu.
  pose proof Hv32 as Hv.
  
  
  (* 证明各部分在范围内 *)
  assert (Hul_bounds: 0 <= Z.land u_pre 65535 < 65536) by (apply land_65535_bounds_alt).
  assert (Hvl_bounds: 0 <= Z.land v_pre 65535 < 65536) by (apply land_65535_bounds_alt).
  assert (Huh_bounds: 0 <= Z.shiftr u_pre 16 < 65536) by (apply shiftr_16_full_bounds; exact Hu).
  assert (Hvh_bounds: 0 <= Z.shiftr v_pre 16 < 65536) by (apply shiftr_16_full_bounds; exact Hv).
  
  (* 各乘积在 [0, 2^32) 范围内 *)
  assert (Hx0_small: 0 <= Z.land u_pre 65535 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx1_small: 0 <= Z.land u_pre 65535 * Z.shiftr v_pre 16 < 4294967296) by nia.
  assert (Hx2_small: 0 <= Z.shiftr u_pre 16 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx3_small: 0 <= Z.shiftr u_pre 16 * Z.shiftr v_pre 16 < 4294967296) by nia.
  
  (* 简化 mod 操作 *)
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.shiftr v_pre 16) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.shiftr v_pre 16) 4294967296) by lia.
  
  exact Hlemma.
Qed.

Lemma proof_of_gmp_umul_ppmm_return_wit_2 : gmp_umul_ppmm_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_umul_ppmm_return_wit_2_split_goal_1.
Qed.


Lemma proof_of_mpn_mul_1_entail_wit_1_split_goal_1 :
  mpn_mul_1_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_1_split_goal_2 :
  mpn_mul_1_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_1_split_goal_3 :
  mpn_mul_1_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_1 : mpn_mul_1_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_1_split_goal_3.
Qed.

(* 循环不变式保持引理：无溢出情况 *)

Lemma proof_of_mpn_mul_1_entail_wit_5_1_split_goal_1 :
  mpn_mul_1_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst i.
  - (* 核心不变式 *)
    simpl. apply mpn_mul_1_no_carry_invariant with (vl_pre := vl_pre); try lia; auto.
    + unfold UINT_MOD. lia.
    + assert (Hw0: 0 <= lpl < UINT_MOD) by (unfold UINT_MOD in *; lia). unfold UINT_MOD in *. lia.
    + assert (Hw1: 0 <= hpl < UINT_MOD) by (unfold UINT_MOD in *; lia). unfold UINT_MOD in *. lia.
    + unfold UINT_MOD. lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_1_split_goal_2 :
  mpn_mul_1_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply list_within_bound_concat; auto.
  simpl; split; auto.
  unfold unsigned_last_nbits, UINT_MOD.
  pose proof (Z.mod_pos_bound (lpl + cl) (2 ^ 32)).
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_1_split_goal_3 :
  mpn_mul_1_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_1 : mpn_mul_1_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_1_split_goal_3.
Qed.

(* 循环出口：返回结果 *)

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_1 :
  mpn_mul_1_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst i.
  simpl.
  apply mpn_mul_1_carry_invariant with (vl_pre := vl_pre); try lia; auto.
  - unfold UINT_MOD. lia.
  - assert (Hw0: 0 <= lpl < UINT_MOD) by (unfold UINT_MOD in *; lia).
    exact Hw0.
  - assert (Hw1: 0 <= hpl < UINT_MOD) by (unfold UINT_MOD in *; lia).
    exact Hw1.
  - unfold UINT_MOD. lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_2 :
  mpn_mul_1_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply list_within_bound_concat; auto.
  simpl; split; auto.
  unfold unsigned_last_nbits, UINT_MOD.
  pose proof (Z.mod_pos_bound (lpl + cl) (2 ^ 32)).
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_3 :
  mpn_mul_1_entail_wit_5_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_4 :
  mpn_mul_1_entail_wit_5_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold unsigned_last_nbits, UINT_MOD.
  pose proof (Z.mod_pos_bound (1 + hpl) (2 ^ 32)).
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_5 :
  mpn_mul_1_entail_wit_5_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold unsigned_last_nbits, UINT_MOD.
  pose proof (Z.mod_pos_bound (1 + hpl) (2 ^ 32)).
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2 : mpn_mul_1_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - (* 分离逻辑：数组合并 *)
    Goal_apply proof_of_mpn_mul_1_entail_wit_5_2_split_goal_1.
  - (* 核心不变式 *)
    Goal_apply proof_of_mpn_mul_1_entail_wit_5_2_split_goal_2.
  - (* list_within_bound *)
    Goal_apply proof_of_mpn_mul_1_entail_wit_5_2_split_goal_3.
  - (* Zlength *)
    Goal_apply proof_of_mpn_mul_1_entail_wit_5_2_split_goal_4.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_2_split_goal_5.
Qed.

(* 循环不变式保持引理：溢出情况 *)

Lemma proof_of_mpn_mul_1_return_wit_1 : mpn_mul_1_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (list_to_Z UINT_MOD l_rp) l_rp.
  split_pure_spatial.
  - assert (Hi_eq: i = n_pre) by lia. rewrite Hi_eq.
    rewrite (UIntArray.undef_seg_empty rp_pre n_pre).
    normalize.
    cancel.
    sep_apply UIntArray.seg_to_full.
    replace (rp_pre + 0 * sizeof ( UINT )) with rp_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    assert (Hi_eq: i = n_pre) by lia. rewrite Hi_eq in *.
    rewrite (sublist_self l n_pre) in PreH8 by lia. lia.
Qed. 
