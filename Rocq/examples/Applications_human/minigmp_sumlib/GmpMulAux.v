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
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import gmp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import GmpAux GmpNumber.
Import Aux.
Local Open Scope sac.

(* ============================================================
   第一部分：位运算辅助引理
   ============================================================ *)

Lemma land_65535_bounds_alt: forall x, 0 <= Z.land x 65535 < 65536.
Proof.
  intros.
  assert (H65535: 65535 = Z.ones 16) by reflexivity.
  rewrite H65535.
  split.
  - apply Z.land_nonneg. lia.
  - rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound. lia.
Qed.


Lemma shiftr_16_full_bounds: forall x,
  0 <= x < 4294967296 -> 0 <= Z.shiftr x 16 < 65536.
Proof.
  intros x H.
  split.
  - apply Z.shiftr_nonneg. lia.
  - rewrite Z.shiftr_div_pow2 by lia.
    assert (65536 = 2^16) by reflexivity.
    rewrite H0.
    apply Z.div_lt_upper_bound; lia.
Qed.

(* ============================================================
   第三部分：进位条件转换引理

   unsigned_last_nbits 的恒等化和取模化直接复用 IntLib 中的
   unsigned_last_nbits_eq / unsigned_Lastnbits_mod_correct，不在本文件
   重复定义 32-bit 专用版本。
   ============================================================ *)

(* 将VC中的进位条件形式转换为引理所需的形式 *)

Lemma carry_condition_transform : forall u_pre v_pre,
  0 <= u_pre < 4294967296 ->
  0 <= v_pre < 4294967296 ->
  let ul := Z.land u_pre 65535 in
  let uh := Z.shiftr u_pre 16 in
  let vl := Z.land v_pre 65535 in
  let vh := Z.shiftr v_pre 16 in
  let x0 := ul * vl in
  let x1 := ul * vh in
  let x2 := uh * vl in
  (* H 中的形式 *)
  unsigned_last_nbits
    (unsigned_last_nbits
       (unsigned_last_nbits x1 32 +
        Z.shiftr (unsigned_last_nbits x0 32) 16) 32 +
     unsigned_last_nbits x2 32) 32 <
  unsigned_last_nbits x2 32 ->
  (* 目标形式 *)
  unsigned_last_nbits
    (((x1 + Z.shiftr x0 16) mod 4294967296 + x2) mod 4294967296) 32 <
  unsigned_last_nbits x2 32.
Proof.
  intros u_pre v_pre Hu Hv.
  cbn zeta.
  intros H.
  set (ul := Z.land u_pre 65535) in *.
  set (uh := Z.shiftr u_pre 16) in *.
  set (vl := Z.land v_pre 65535) in *.
  set (vh := Z.shiftr v_pre 16) in *.
  set (x0 := ul * vl) in *.
  set (x1 := ul * vh) in *.
  set (x2 := uh * vl) in *.
  
  (* 证明 x0, x1, x2 都在小范围内 *)
  assert (Hx0_bounds: 0 <= x0 < 4294967296).
  { unfold x0, ul, vl.
    pose proof (land_65535_bounds_alt u_pre) as Hul.
    pose proof (land_65535_bounds_alt v_pre) as Hvl.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - nia. }
  assert (Hx1_bounds: 0 <= x1 < 4294967296).
  { unfold x1, ul, vh.
    pose proof (land_65535_bounds_alt u_pre) as Hul.
    pose proof (shiftr_16_full_bounds v_pre Hv) as Hvh.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - nia. }
  assert (Hx2_bounds: 0 <= x2 < 4294967296).
  { unfold x2, uh, vl.
    pose proof (shiftr_16_full_bounds u_pre Hu) as Huh.
    pose proof (land_65535_bounds_alt v_pre) as Hvl.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - nia. }
  
  (* 简化 H 中有显式边界的 unsigned_last_nbits。 *)
  rewrite (unsigned_last_nbits_eq x1 32) in H by lia.
  rewrite (unsigned_last_nbits_eq x0 32) in H by lia.
  rewrite (unsigned_last_nbits_eq x2 32) in H by lia.
  
  (* 剩余的 unsigned_last_nbits 转成模 2^32 的形式。 *)
  unfold unsigned_last_nbits in H.
  change (2 ^ 32) with 4294967296 in H.
  
  (* 目标转换 *)
  unfold unsigned_last_nbits.
  change (2 ^ 32) with 4294967296.
  rewrite Zmod_mod by lia.
  rewrite (Z.mod_small x2 4294967296) by lia.
  exact H.
Qed.


(* ============================================================
   第六部分：gmp_umul_ppmm 正确性证明
   
   算法：32位×32位乘法，结果为64位(w1:w0)
   将u,v分解为高低16位，计算部分积后合并
   证明目标：w1 * 2^32 + w0 = u * v
   ============================================================ *)


Lemma mpn_mul_1_no_carry_invariant :
  forall (l_rp_2 l : list Z) (cl i w0_value w1_value vl_pre : Z),
    0 <= i ->
    i < Zlength l ->
    0 <= cl < UINT_MOD ->
    0 <= w0_value < UINT_MOD ->
    0 <= w1_value < UINT_MOD ->
    0 <= vl_pre < UINT_MOD ->
    Zlength l_rp_2 = i ->
    list_within_bound UINT_MOD l_rp_2 ->
    list_within_bound UINT_MOD l ->
    (* 乘法结果 *)
    w1_value * UINT_MOD + w0_value = Znth i l 0 * vl_pre ->
    (* 之前的循环不变式 *)
    list_to_Z UINT_MOD l_rp_2 + cl * UINT_MOD ^ i = 
      list_to_Z UINT_MOD (sublist 0 i l) * vl_pre ->
    (* 无溢出条件 *)
    unsigned_last_nbits (w0_value + cl) 32 >= cl ->
    (* 新的循环不变式 *)
    list_to_Z UINT_MOD (l_rp_2 ++ (unsigned_last_nbits (w0_value + cl) 32 :: nil)) + 
      w1_value * UINT_MOD ^ (i + 1) =
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) * vl_pre.
Proof.
  intros l_rp_2 l cl i w0_value w1_value vl_pre.
  intros Hi_pos Hi_bound Hcl_bound Hw0_bound Hw1_bound Hvl_bound.
  intros Hlen Hl_rp_bound Hl_bound Hmul Hinv Hno_overflow.
  
  (* 关键观察：无溢出条件意味着 w0_value + cl < UINT_MOD *)
  assert (Hsum_small: w0_value + cl < UINT_MOD).
  {
    unfold unsigned_last_nbits in Hno_overflow.
    unfold UINT_MOD in *.
    destruct (Z_lt_ge_dec (w0_value + cl) (2^32)).
    - lia.
    - (* 如果 w0_value + cl >= 2^32，则 mod 后 < cl，矛盾 *)
      rewrite Z.mod_eq in Hno_overflow by lia.
      assert (Hdiv_ge_1: (w0_value + cl) / 2^32 >= 1).
      { 
        assert (H2pow: 0 < 2^32) by lia.
        assert (Hle: 2^32 <= w0_value + cl) by lia.
        pose proof (Z.div_le_mono (2^32) (w0_value + cl) (2^32) H2pow Hle).
        rewrite Z.div_same in H by lia.
        lia.
      }
      lia.
  }
  
  (* 因此 unsigned_last_nbits (w0_value + cl) 32 = w0_value + cl *)
  assert (Hunsigned_eq: unsigned_last_nbits (w0_value + cl) 32 = w0_value + cl).
  {
    unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_small; lia.
  }
  
  rewrite Hunsigned_eq.
  
  (* 展开 list_to_Z 的追加 *)
  assert (HUINT_MOD_pos: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  rewrite (list_to_Z_concat_r UINT_MOD HUINT_MOD_pos l_rp_2 (w0_value + cl)).
  2: { unfold UINT_MOD in *. lia. }
  rewrite Hlen.
  
  (* 展开 sublist 0 (i+1) l *)
  rewrite (list_to_Z_list_append UINT_MOD HUINT_MOD_pos l i); try lia.
  2: { exact Hl_bound. }
  
  (* 引入变量以便处理 *)
  set (L := list_to_Z UINT_MOD (sublist 0 i l)) in *.
  set (X := Znth i l 0) in *.
  set (M := UINT_MOD) in *.
  set (P := M ^ i) in *.
  
  (* 将 LHS 中的 list_to_Z l_rp_2 用 Hinv 替换 *)
  assert (Hlist_eq: list_to_Z M l_rp_2 = L * vl_pre - cl * P) by lia.
  rewrite Hlist_eq.
  
  (* 展开 M ^ (i + 1) = M * P *)
  assert (Hpow: M ^ (i + 1) = M * P).
  { unfold P. rewrite Z.pow_add_r by lia. ring. }
  rewrite Hpow.
  
  (* 现在目标是代数等式 *)
  (* LHS: (w0_value + cl) * P + (L * vl_pre - cl * P) + w1_value * (M * P) *)
  (* RHS: (L + X * P) * vl_pre *)
  
  (* 使用 Hmul: w1_value * M + w0_value = X * vl_pre *)
  assert (Hxvl: X * vl_pre = w1_value * M + w0_value) by lia.
  
  (* 展开 RHS *)
  replace ((L + X * P) * vl_pre) with (L * vl_pre + X * vl_pre * P) by ring.
  rewrite Hxvl.
  
  (* 现在目标是:
     (w0_value + cl) * P + (L * vl_pre - cl * P) + w1_value * (M * P) 
     = L * vl_pre + (w1_value * M + w0_value) * P *)
  ring.
Qed.

(* 循环体：无溢出分支 *)

Lemma mpn_mul_1_carry_invariant :
  forall (l_rp_2 l : list Z) (cl i w0_value w1_value vl_pre : Z),
    0 <= i ->
    i < Zlength l ->
    0 <= cl < UINT_MOD ->
    0 <= w0_value < UINT_MOD ->
    0 <= w1_value < UINT_MOD ->
    0 <= vl_pre < UINT_MOD ->
    Zlength l_rp_2 = i ->
    list_within_bound UINT_MOD l_rp_2 ->
    list_within_bound UINT_MOD l ->
    (* 乘法结果 *)
    w1_value * UINT_MOD + w0_value = Znth i l 0 * vl_pre ->
    (* 之前的循环不变式 *)
    list_to_Z UINT_MOD l_rp_2 + cl * UINT_MOD ^ i = 
      list_to_Z UINT_MOD (sublist 0 i l) * vl_pre ->
    (* 溢出条件 *)
    unsigned_last_nbits (w0_value + cl) 32 < cl ->
    (* 新的循环不变式 *)
    list_to_Z UINT_MOD (l_rp_2 ++ (unsigned_last_nbits (w0_value + cl) 32 :: nil)) + 
      unsigned_last_nbits (1 + w1_value) 32 * UINT_MOD ^ (i + 1) =
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) * vl_pre.
Proof.
  intros l_rp_2 l cl i w0_value w1_value vl_pre.
  intros Hi_pos Hi_bound Hcl_bound Hw0_bound Hw1_bound Hvl_bound.
  intros Hlen Hl_rp_bound Hl_bound Hmul Hinv Hoverflow.
  
  (* 关键观察：溢出条件意味着 w0_value + cl >= UINT_MOD *)
  assert (Hsum_large: w0_value + cl >= UINT_MOD).
  {
    unfold unsigned_last_nbits in Hoverflow.
    unfold UINT_MOD in *.
    destruct (Z_lt_ge_dec (w0_value + cl) (2^32)).
    - (* 如果 w0_value + cl < 2^32，则 mod 后 = 原值 >= cl，矛盾 *)
      rewrite Z.mod_small in Hoverflow by lia. lia.
    - lia.
  }
  
  (* 计算 unsigned_last_nbits (w0_value + cl) 32 = w0_value + cl - UINT_MOD *)
  assert (Hunsigned_eq: unsigned_last_nbits (w0_value + cl) 32 = w0_value + cl - UINT_MOD).
  {
    unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_eq by lia.
    assert (Hdiv1: (w0_value + cl) / 2^32 = 1).
    {
      assert (w0_value + cl < 2 * 2^32) by lia.
      assert (w0_value + cl >= 2^32) by lia.
      assert (H2pow: 0 < 2^32) by lia.
      assert (Hdiv_ge: 1 <= (w0_value + cl) / 2^32).
      { 
        apply Z.div_le_lower_bound; try lia.
        (* 需要证明 1 * 2^32 <= w0_value + cl *)
      }
      assert (Hdiv_lt: (w0_value + cl) / 2^32 < 2).
      { 
        apply Z.div_lt_upper_bound; try lia.
        (* 需要证明 w0_value + cl < 2 * 2^32 *)
      }
      lia.
    }
    lia.
  }
  
  (* 计算 unsigned_last_nbits (1 + w1_value) 32 *)
  (* 由于 w1_value <= UINT_MAX - 1 (因为乘法的高位最多是 UINT_MAX - 1)，
     所以 1 + w1_value <= UINT_MAX < UINT_MOD *)
  assert (Hw1_upper: w1_value <= UINT_MOD - 2).
  {
    (* w1_value * UINT_MOD + w0_value = Znth i l 0 * vl_pre *)
    (* Znth i l 0 < UINT_MOD, vl_pre < UINT_MOD *)
    (* 所以 Znth i l 0 * vl_pre <= (UINT_MOD - 1) * (UINT_MOD - 1) < UINT_MOD^2 - UINT_MOD *)
    assert (HZnth_bound: 0 <= Znth i l 0 < UINT_MOD).
    { apply list_within_bound_Znth_bound; auto; lia. }
    assert (Znth i l 0 * vl_pre <= (UINT_MOD - 1) * (UINT_MOD - 1)).
    { apply Z.mul_le_mono_nonneg; lia. }
    assert ((UINT_MOD - 1) * (UINT_MOD - 1) = UINT_MOD * UINT_MOD - 2 * UINT_MOD + 1).
    { unfold UINT_MOD. ring. }
    assert (w1_value * UINT_MOD <= UINT_MOD * UINT_MOD - 2 * UINT_MOD + 1 - w0_value) by lia.
    assert (w1_value * UINT_MOD <= UINT_MOD * UINT_MOD - 2 * UINT_MOD + 1) by lia.
    (* 直接用 nia 证明 w1_value <= UINT_MOD - 2 *)
    unfold UINT_MOD in *.
    nia.
  }
  
  assert (Hunsigned_w1: unsigned_last_nbits (1 + w1_value) 32 = 1 + w1_value).
  {
    unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_small; lia.
  }
  
  rewrite Hunsigned_eq.
  rewrite Hunsigned_w1.
  
  (* 展开 list_to_Z 的追加 *)
  assert (HUINT_MOD_pos: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  rewrite (list_to_Z_concat_r UINT_MOD HUINT_MOD_pos l_rp_2 (w0_value + cl - UINT_MOD)).
  2: { unfold UINT_MOD in *. lia. }
  rewrite Hlen.
  
  (* 展开 sublist 0 (i+1) l *)
  rewrite (list_to_Z_list_append UINT_MOD HUINT_MOD_pos l i); try lia.
  2: { exact Hl_bound. }
  
  (* 引入变量以便处理 *)
  set (L := list_to_Z UINT_MOD (sublist 0 i l)) in *.
  set (X := Znth i l 0) in *.
  set (M := UINT_MOD) in *.
  set (P := M ^ i) in *.
  
  (* 将 LHS 中的 list_to_Z l_rp_2 用 Hinv 替换 *)
  assert (Hlist_eq: list_to_Z M l_rp_2 = L * vl_pre - cl * P) by lia.
  rewrite Hlist_eq.
  
  (* 展开 M ^ (i + 1) = M * P *)
  assert (Hpow: M ^ (i + 1) = M * P).
  { unfold P. rewrite Z.pow_add_r by lia. ring. }
  rewrite Hpow.
  
  (* 使用 Hmul: w1_value * M + w0_value = X * vl_pre *)
  assert (Hxvl: X * vl_pre = w1_value * M + w0_value) by lia.
  
  (* 展开 RHS *)
  replace ((L + X * P) * vl_pre) with (L * vl_pre + X * vl_pre * P) by ring.
  rewrite Hxvl.
  
  (* 现在目标是代数等式 *)
  ring.
Qed.

(* 循环体：溢出分支 *)
