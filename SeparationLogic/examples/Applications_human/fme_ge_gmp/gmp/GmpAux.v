Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import CommonAssertion Mem SeparationLogic IntLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.
Import naive_C_Rules.
Local Open Scope sac.

Module Aux.

Lemma Zdiv_ge_1_larger : forall a b, 1 <= b -> 0 <= a -> a / b >= 1 -> a >= b.
Proof.
  intros.
  destruct (Z_lt_dec a b) ; try lia.
  rewrite Z.div_small in H1 by lia.
  lia.
Qed.

Lemma Z_mod_add_carry: forall (a b m: Z),
   m > 0 -> 0 <= a < m -> 0 <= b < m ->
   (a + b) mod m < b ->
   a + b = (a + b) mod m + m.
Proof.
  intros.
  pose proof (Z_div_mod_eq_full (a + b) m).
  assert (m <= a + b < 2 * m). {
    assert (a + b >= m \/ b <= a + b < m). { lia. }
    destruct H4.
    + lia.
    + assert ((a + b) mod m = a + b). { 
        apply Z.mod_small.
        lia.
      }
      lia.
  }
  assert ((a + b) / m = 1). {
    pose proof (Zdiv_le_lower_bound (a + b) m 1 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (a + b) m 2 ltac:(lia) ltac:(lia)).
    lia.
  }
  rewrite H5 in H3.
  nia.
Qed.

Lemma Z_mod_add_uncarry: forall (a b m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m ->
  (a + b) mod m >= b ->
  a + b = (a + b) mod m.
Proof.
  intros.
  assert (b <= a + b < m). {
    assert (a + b < m \/ m <= a + b < m + b). { lia. }
    destruct H3.
    + lia.
    + assert ((a + b) / m = 1). { 
        pose proof (Zdiv_le_lower_bound (a + b) m 1 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_lt_upper_bound (a + b) m 2 ltac:(lia) ltac:(lia)).
        lia.
      }
      pose proof (Z_div_mod_eq_full (a + b) m).
      rewrite H4 in H5.
      lia.
  }
  rewrite Z.mod_small; lia.
Qed.

(* 辅助引理：如果 a + b >= m，则 (a + b) mod m < b *)
Lemma Z_mod_add_carry_condition: forall (a b m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m ->
  a + b >= m ->
  (a + b) mod m < b.
Proof.
  intros.
  (* 由于 m <= a + b < 2*m，我们有 (a+b) mod m = a + b - m *)
  assert (Hbound: m <= a + b < 2 * m) by lia.
  (* 使用 Z.add_mod_idemp_l 和 Z.mod_small *)
  replace (a + b) with ((a + b - m) + m) by ring.
  rewrite Z.add_mod by lia.
  rewrite Z.mod_same by lia.
  rewrite Z.add_0_r.
  rewrite Z.mod_mod by lia.
  rewrite Z.mod_small by lia.
  lia.
Qed.

Lemma Z_mod_3add_carry10: forall (a b c m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m -> 0 <= c < m ->
  (a + c) mod m < c ->
  ((a + c) mod m + b) mod m >= b ->
  a + b + c = ((a + c) mod m + b) mod m + m.
Proof.
  intros.
  assert (a + c = (a + c) mod m + m). {
    apply Z_mod_add_carry; try lia.
  }
  assert ((a + c) mod m + b = ((a + c) mod m + b) mod m). {
    apply Z_mod_add_uncarry; try lia.
    apply Z.mod_pos_bound.
    lia.
  }
  rewrite <-H6.
  assert ((a + c) mod m + b + m = (a + c) mod m + m + b) by lia.
  rewrite H7.
  rewrite <-H5.
  lia.
Qed.

Lemma Z_mod_3add_carry01: forall (a b c m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m -> 0 <= c < m ->
  (a + c) mod m >= c ->
  ((a + c) mod m + b) mod m < b ->
  a + b + c = ((a + c) mod m + b) mod m + m.
Proof.
  intros.
  assert (a + c = (a + c) mod m). {
    apply Z_mod_add_uncarry; try lia.
  }
  assert ((a + c) mod m + b = ((a + c) mod m + b) mod m + m). {
    apply Z_mod_add_carry; try lia.
    apply Z.mod_pos_bound.
    lia.
  }
  rewrite <-H6.
  rewrite <-H5.
  lia.
Qed.

Lemma Z_mod_3add_carry11: forall (a b c m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m -> 0 <= c < m ->
  (a + c) mod m < c ->
  ((a + c) mod m + b) mod m < b ->
  a + b + c = ((a + c) mod m + b) mod m + m * 2.
Proof.
  intros.
  assert (a + c = (a + c) mod m + m). {
    apply Z_mod_add_carry; try lia.
  }
  assert ((a + c) mod m + b = ((a + c) mod m + b) mod m + m). {
    apply Z_mod_add_carry; try lia.
    apply Z.mod_pos_bound.
    lia.
  }
  assert (((a + c) mod m + b) mod m + m * 2 = ((a + c) mod m + b) mod m + m + m) by lia.
  rewrite H7.
  rewrite <-H6.
  assert ((a + c) mod m + b + m = (a + c) mod m + m + b) by lia.
  rewrite H8.
  rewrite <-H5.
  lia.
Qed.

Lemma Z_mod_3add_carry00: forall (a b c m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m -> 0 <= c < m ->
  (a + c) mod m >= c ->
  ((a + c) mod m + b) mod m >= b ->
  a + b + c = ((a + c) mod m + b) mod m.
Proof.
  intros.
  assert (a + c = (a + c) mod m). {
    apply Z_mod_add_uncarry; try lia.
  }
  assert ((a + c) mod m + b = ((a + c) mod m + b) mod m). {
    apply Z_mod_add_uncarry; try lia.
    apply Z.mod_pos_bound.
    lia.
  }
  rewrite <-H6.
  rewrite <-H5.
  lia.
Qed.

Lemma Z_of_nat_succ: forall (n: nat),
  Z.of_nat (S n) = Z.of_nat n + 1.
Proof. lia. Qed.

Lemma Zpow_add_1: forall (a b: Z),
  a >= 0 -> b >= 0 ->
  a ^ (b + 1) = a ^ b * a.
Proof.
  intros.
  rewrite (Z.pow_add_r a b 1); lia.
Qed.

Lemma Zmul_mod_cancel: forall (n a b: Z),
  n >= 0 -> a > 0 -> b >= 0 ->
  (n * a) mod (a ^ (b + 1)) = a * (n mod (a ^ b)).
Proof.
  intros.
  pose proof (Z_div_mod_eq_full n (a ^ b)).
  pose proof (Z.mod_bound_pos n (a ^ b) ltac:(lia) ltac:(nia)).
  remember (n / a ^ b) as q eqn:Hq.
  remember (n mod a ^ b) as rem eqn:Hrem.
  rewrite H2.
  rewrite Z.mul_add_distr_r.
  rewrite (Z.mul_comm (a ^ b) q); rewrite <-Z.mul_assoc.
  rewrite <-Zpow_add_1; try lia.
  assert (0 <= rem * a < a ^ (b + 1)). { 
    rewrite Zpow_add_1; try lia.
    nia.
  }
  rewrite <-(Zmod_unique_full (q * a ^ (b + 1) + rem * a) (a ^ (b + 1)) q (rem * a)).
  + lia.
  + unfold Remainder.
    lia.
  + lia.
Qed.

Lemma Zdiv_mod_pow: forall (n a b: Z),
  a > 0 -> b >= 0 -> n >= 0 ->
  (n / a) mod (a ^ b) = (n mod (a ^ (b + 1))) / a.
Proof.
  intros.
  pose proof (Z_div_mod_eq_full n (a ^ (b + 1))).
  remember (n / (a ^ (b + 1))) as q eqn:Hq.
  remember (n mod a ^ (b + 1)) as rem eqn:Hrem.
  assert (n / a = a ^ b * q + rem / a). {
    rewrite H2.
    rewrite Zpow_add_1; try lia.
    pose proof (Z_div_plus_full_l (a ^ b * q) a rem ltac:(lia)).
    assert (a ^ b * q * a + rem = a ^ b * a * q + rem). { lia. }
    rewrite H4 in H3.
    tauto.
  }
  apply Znumtheory.Zdivide_mod_minus.
  + pose proof (Z.mod_bound_pos n (a ^ (b + 1)) ltac:(lia) (Z.pow_pos_nonneg a (b + 1) ltac:(lia) ltac:(lia))).
    rewrite <-Hrem in H4.
    rewrite Zpow_add_1 in H4; try lia.
    pose proof (Z.div_lt_upper_bound rem a (a ^ b) ltac:(lia) ltac:(lia)).
    split; try lia.
    apply (Z_div_pos rem a ltac:(lia) ltac:(lia)).
  + unfold Z.divide.
    exists q.
    lia.
Qed.

Lemma list_app_cons: forall (l1 l2: list Z) (a: Z),
  app l1 (a :: l2) = app (app l1 (a :: nil)) l2.
Proof.
  intros.
  revert a l2.
  induction l1.
  + intros.
    rewrite app_nil_l.
    reflexivity.
  + intros.
    simpl in *.
    specialize (IHl1 a0 l2).
    rewrite IHl1.
    reflexivity.
Qed.

Lemma list_app_single_l: forall (l: list Z) (a: Z),
  ([a] ++ l)%list = a :: l.
Proof.
  intros.
  induction l.
  + simpl; reflexivity.
  + rewrite list_app_cons.
    simpl.
    reflexivity.
Qed.

Lemma list_last_cons: forall (a: Z) (l: list Z),
  l <> nil ->
  last (a :: l) 1 = last l 1.
Proof.
  intros.
  destruct l.
  + contradiction.
  + simpl.
    reflexivity.
Qed.

Lemma list_last_to_Znth: forall (l: list Z),
  l <> nil ->
  last l 1 = Znth ((Zlength l) - 1) l 0.
Proof.
  intros.
  induction l.
  + contradiction.
  + destruct l.
    - simpl.
      rewrite Znth0_cons.
      lia.
    - pose proof (@nil_cons Z z l).
      specialize (IHl ltac:(auto)); clear H0.
      rewrite list_last_cons; [ | pose proof (@nil_cons Z z l); auto ].
      rewrite IHl.
      pose proof (Zlength_cons a (z :: l)).
      unfold Z.succ in H0; rewrite H0; clear H0.
      pose proof (Zlength_nonneg l).
      pose proof (Zlength_cons z l); unfold Z.succ in H1.
      pose proof (Znth_cons 0 (Zlength (z :: l)) a (z :: l) (ltac:(lia))).
      assert (Zlength (z :: l) + 1 - 1 = Zlength (z :: l)). { lia. }
      rewrite H3; clear H3.
      rewrite H2.
      reflexivity.
Qed.

Lemma Zlength_removelast: forall (l: list Z),
  l <> [] ->
  Zlength (removelast l) = Zlength l - 1.
Proof.
  intros.
  induction l.
  + contradiction.
  + destruct l.
    - simpl.
      rewrite Zlength_nil.
      lia.
    - pose proof (@nil_cons Z z l).
      specialize (IHl ltac:(auto)).
      assert (removelast (a :: z :: l) = a :: removelast(z :: l)). {
        simpl.
        reflexivity.
      }
      rewrite H1; clear H1.
      repeat rewrite Zlength_cons; unfold Z.succ.
      rewrite IHl.
      rewrite Zlength_cons; unfold Z.succ.
      lia.
Qed.

Lemma store_array_rec_snoc: forall (l: list Z) (v: Z) (rp lo hi: Z),
  0 <= lo ->
  hi = lo + Zlength l ->
  store_array_rec (fun (x : addr) (lo a : Z) => (x + lo * sizeof ( UINT )) # UInt |-> a) rp lo hi l **
      (rp + hi * sizeof(UINT)) # UInt |-> v
  |-- store_array_rec (fun (x : addr) (lo a : Z) => (x + lo * sizeof ( UINT )) # UInt |-> a) rp lo (hi + 1) (l ++ v :: nil).
Proof.
  intros l.
  induction l; intros.
  - simpl.
    rewrite Zlength_nil in H0.
    subst hi.
    simpl.
    replace (lo + 0) with lo by lia.
    replace (lo + 0 + 1) with (lo + 1) by lia.
    entailer!.
  - simpl.
    rewrite Zlength_cons in H0.
    unfold Z.succ in H0.
    assert (Hhi: hi = lo + 1 + Zlength l) by lia.
    sep_apply (IHl v rp (lo + 1) hi ltac:(lia) Hhi).
    entailer!.
Qed.

Lemma UIntArray_full_snoc: forall (l: list Z) (v: Z) (rp: Z),
  UIntArray.full rp (Zlength l) l ** (rp + (Zlength l) * sizeof(UINT)) # UInt |-> v
  |-- UIntArray.full rp (Zlength l + 1) (l ++ v :: nil).
Proof.
  intros.
  unfold UIntArray.full, store_array.
  apply store_array_rec_snoc; lia.
Qed.

(* 更通用的版本，允许 n 和 Zlength l 形式上不同 *)
Lemma UIntArray_full_snoc': forall (l: list Z) (v: Z) (rp n: Z),
  n = Zlength l ->
  UIntArray.full rp n l ** (rp + n * sizeof(UINT)) # UInt |-> v
  |-- UIntArray.full rp (n + 1) (l ++ v :: nil).
Proof.
  intros.
  unfold UIntArray.full, store_array.
  sep_apply (store_array_rec_snoc l v rp 0 n); try lia.
  entailer!.
Qed.

(* 保留数组的同时提取长度信息 *)
Lemma UIntArray_full_Zlength_preserve: forall (rp n: Z) (l: list Z),
  UIntArray.full rp n l |-- “ Zlength l = n ” && UIntArray.full rp n l.
Proof.
  intros.
  apply logic_equiv_coq_prop_andp1.
  apply UIntArray.full_Zlength.
Qed.

(* 保留 UInt 存储的同时提取范围约束 *)
Lemma store_uint_range_preserve: forall (x: addr) (v: Z),
  x # UInt |-> v |-- “ 0 <= v <= Int.max_unsigned ” && x # UInt |-> v.
Proof.
  intros.
  apply logic_equiv_coq_prop_andp1.
  apply store_uint_range.
Qed.

Lemma Z_mod_neg: forall x m,
  m > 0 -> -m < x < 0 -> x mod m = x + m.
Proof.
  intros.
  rewrite <- Z.mod_add with (b := 1) by lia.
  rewrite Z.mod_small by lia.
  ring.
Qed.

(* Lemmas for 32-bit unsigned multiplication using 16-bit parts *)
Lemma umul_split: forall (u v : Z),
  0 <= u < 4294967296 ->
  0 <= v < 4294967296 ->
  u * v = (Z.shiftr u 16) * (Z.shiftr v 16) * 4294967296 +
          ((Z.shiftr u 16) * (Z.land v 65535) + (Z.land u 65535) * (Z.shiftr v 16)) * 65536 +
          (Z.land u 65535) * (Z.land v 65535).
Proof.
  intros.
  rewrite !Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod u (2^16) ltac:(lia)) as Hu.
  pose proof (Z.div_mod v (2^16) ltac:(lia)) as Hv.
  assert (Hland_u: Z.land u 65535 = u mod 2^16). {
    assert (65535 = Z.ones 16) by reflexivity.
    rewrite H1. apply Z.land_ones. lia.
  }
  assert (Hland_v: Z.land v 65535 = v mod 2^16). {
    assert (65535 = Z.ones 16) by reflexivity.
    rewrite H1. apply Z.land_ones. lia.
  }
  rewrite Hland_u, Hland_v.
  rewrite Hu at 1. rewrite Hv at 1.
  assert (65536 = 2^16) by reflexivity.
  assert (4294967296 = 2^32) by reflexivity.
  rewrite H1, H2. nia.
Qed.

Lemma land_65535_eq: forall x,
  0 <= x < 65536 ->
  Z.land x 65535 = x.
Proof.
  intros.
  assert (65535 = Z.ones 16) by reflexivity.
  assert (65536 = 2^16) by reflexivity.
  rewrite H0. rewrite Z.land_ones by lia.
  rewrite H1 in H.
  apply Z.mod_small. lia.
Qed.

Lemma shiftr_16_bounds: forall x,
  0 <= x < 4294967296 ->
  0 <= Z.shiftr x 16 < 65536.
Proof.
  intros.
  assert (4294967296 = 2^32) by reflexivity.
  assert (65536 = 2^16) by reflexivity.
  split.
  - apply Z.shiftr_nonneg. lia.
  - rewrite Z.shiftr_div_pow2 by lia.
    rewrite H0, H1 in *.
    apply Z.div_lt_upper_bound; lia.
Qed.

Lemma land_65535_bounds: forall x,
  0 <= x < 4294967296 ->
  0 <= Z.land x 65535 < 65536.
Proof.
  intros.
  assert (65535 = Z.ones 16) by reflexivity.
  assert (65536 = 2^16) by reflexivity.
  split.
  - apply Z.land_nonneg. left. lia.
  - rewrite H0. rewrite Z.land_ones by lia.
    rewrite H1.
    apply Z.mod_pos_bound. lia.
Qed.

(* 辅助引理：关于左移的关键性质 - 移到前面以便后面使用 *)
Lemma shiftl_16_mod_low: forall x,
  0 <= x < 4294967296 ->
  (Z.shiftl x 16) mod 4294967296 = ((x mod 65536) * 65536) mod 4294967296.
Proof.
  intros.
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (H16: 65536 = 2^16) by reflexivity.
  assert (H32: 4294967296 = 2^32) by reflexivity.
  rewrite H16, H32.
  
  (* x = q * 2^16 + r, where q = x / 2^16 and r = x mod 2^16 *)
  pose proof (Z.div_mod x (2^16) ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound x (2^16) ltac:(lia)) as Hmod_bound.
  
  (* x * 2^16 = (q * 2^16 + r) * 2^16 = q * 2^32 + r * 2^16 *)
  assert (Hexpand: x * 2^16 = (x / 2^16) * 2^32 + (x mod 2^16) * 2^16).
  {
    rewrite Hdiv at 1.
    assert (2^32 = 2^16 * 2^16) by (simpl; lia).
    nia.
  }
  
  rewrite Hexpand.
  
  (* Now use the fact that (a * m + b) mod m = b mod m *)
  assert (Hmod: ((x / 2^16) * 2^32 + (x mod 2^16) * 2^16) mod 2^32 = ((x mod 2^16) * 2^16) mod 2^32).
  {
    assert (Hkey: forall a b m, m > 0 -> (a * m + b) mod m = b mod m).
    {
      intros. rewrite Z.add_mod by lia. rewrite Z.mod_mul by lia. 
      rewrite Z.add_0_l. rewrite Z.mod_mod by lia. reflexivity.
    }
    apply Hkey. lia.
  }
  
  exact Hmod.
Qed.

(* 辅助引理：x mod H * H + x mod H 的化简 - 移到前面以便后面使用 *)  
Lemma decompose_by_shift: forall x H,
  H > 0 ->
  0 <= x ->
  x = (x / H) * H + (x mod H).
Proof.
  intros.
  pose proof (Z.div_mod x H ltac:(lia)) as Hdiv.
  rewrite Z.mul_comm in Hdiv.
  exact Hdiv.
Qed.

Lemma umul_ppmm_correct_with_carry: forall u v ul uh vl vh x0 x1 x2 x3,
  0 <= u < 4294967296 ->
  0 <= v < 4294967296 ->
  ul = Z.land u 65535 ->
  uh = Z.shiftr u 16 ->
  vl = Z.land v 65535 ->
  vh = Z.shiftr v 16 ->
  x0 = ul * vl ->
  x1 = ul * vh ->
  x2 = uh * vl ->
  x3 = uh * vh ->
  let x1' := (x1 + Z.shiftr x0 16) mod 4294967296 in
  let x1'' := (x1' + x2) mod 4294967296 in
  x1'' < x2 ->
  let w1 := ((x3 + 65536) mod 4294967296 + Z.shiftr x1'' 16) mod 4294967296 in
  let w0 := ((Z.shiftl x1'' 16) mod 4294967296 + Z.land x0 65535) mod 4294967296 in
  w1 * 4294967296 + w0 = u * v.
Proof.
  intros.
  assert (M32: 4294967296 = 2^32) by reflexivity.
  assert (M16: 65536 = 2^16) by reflexivity.
  assert (M15: 65535 = 2^16 - 1) by reflexivity.
  
  (* 使用 umul_split 展开 u * v *)
  pose proof (umul_split u v H H0) as Hsplit.
  rewrite M32, M16, M15 in Hsplit.
  
  (* 边界条件 *)
  assert (Hx0_bounds: 0 <= x0 < 2^32). {
    rewrite H5, H1, H3.
    pose proof (land_65535_bounds u H) as Hul_b.
    pose proof (land_65535_bounds v H0) as Hvl_b.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - assert (Z.land u 65535 * Z.land v 65535 < 65536 * 65536) by nia.
      nia.
  }
  assert (Hx1_bounds: 0 <= x1 < 2^32). {
    rewrite H6, H1, H4.
    pose proof (land_65535_bounds u H) as Hul_b.
    pose proof (shiftr_16_bounds v H0) as Hvh_b.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - assert (Z.land u 65535 * Z.shiftr v 16 < 65536 * 65536) by nia.
      nia.
  }
  assert (Hx2_bounds: 0 <= x2 < 2^32). {
    rewrite H7, H2, H3.
    pose proof (shiftr_16_bounds u H) as Huh_b.
    pose proof (land_65535_bounds v H0) as Hvl_b.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - assert (Z.shiftr u 16 * Z.land v 65535 < 65536 * 65536) by nia.
      nia.
  }
  assert (Hx3_bounds: 0 <= x3 < 2^32). {
    rewrite H8, H2, H4.
    pose proof (shiftr_16_bounds u H) as Huh_b.
    pose proof (shiftr_16_bounds v H0) as Hvh_b.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - assert (Z.shiftr u 16 * Z.shiftr v 16 < 65536 * 65536) by nia.
      nia.
  }
  assert (Hx1'_bounds: 0 <= x1' < 2^32). {
    unfold x1'. rewrite M32. apply Z.mod_pos_bound. lia.
  }
  assert (Hx1''_bounds: 0 <= x1'' < 2^32). {
    unfold x1''. rewrite M32. apply Z.mod_pos_bound. lia.
  }
  
  (* 关键：由于 x1'' < x2，说明 x1' + x2 发生了进位 *)
  assert (Hcarry: x1' + x2 = x1'' + 2^32). {
    unfold x1''.
    rewrite <- M32.
    assert (Hx1'_b: 0 <= x1' < 4294967296) by (unfold x1'; apply Z.mod_pos_bound; lia).
    assert (Hx2_b: 0 <= x2 < 4294967296) by lia.
    assert (Hcond: (x1' + x2) mod 4294967296 < x2). {
      (* x1'' = (x1' + x2) mod 4294967296 < x2 by H9 *)
      exact H9.
    }
    apply Z_mod_add_carry; lia.
  }
  
  (* 使用 shiftl 和 shiftr 的性质 *)
  assert (Hshiftl: (Z.shiftl x1'' 16) mod 2^32 = (x1'' mod 2^16) * 2^16). {
    pose proof (shiftl_16_mod_low x1'' ltac:(lia)) as Hsl.
    rewrite <- M32, <- M16.
    rewrite Hsl.
    (* 需要证明 (x1'' mod 65536 * 65536) mod 4294967296 = x1'' mod 65536 * 65536 *)
    apply Z.mod_small.
    assert (x1'' mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
    assert (0 <= x1'' mod 65536) by (apply Z.mod_pos_bound; lia).
    nia.
  }
  
  assert (Hshiftr: Z.shiftr x1'' 16 = x1'' / 2^16). {
    rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  }
  
  (* 分解 x1'' = (x1'' / 2^16) * 2^16 + (x1'' mod 2^16) *)
  assert (Hx1''_decomp: x1'' = Z.shiftr x1'' 16 * 2^16 + (x1'' mod 2^16)). {
    rewrite Hshiftr.
    pose proof (Z.div_mod x1'' (2^16) ltac:(lia)) as Hdm.
    lia.
  }
  
  (* 分解 x0 = (x0 / 2^16) * 2^16 + (x0 mod 2^16) *)
  assert (Hx0_decomp: x0 = Z.shiftr x0 16 * 2^16 + Z.land x0 65535). {
    assert (Hland_eq: Z.land x0 65535 = x0 mod 2^16). {
      assert (H65535: 65535 = Z.ones 16) by reflexivity.
      rewrite H65535. rewrite Z.land_ones by lia. reflexivity.
    }
    rewrite Hland_eq.
    assert (Hshiftr_eq: Z.shiftr x0 16 = x0 / 2^16). {
      rewrite Z.shiftr_div_pow2 by lia. reflexivity.
    }
    rewrite Hshiftr_eq.
    pose proof (Z.div_mod x0 (2^16) ltac:(lia)) as Hdm.
    lia.
  }
  
  (* 现在我们需要证明：w1 * 2^32 + w0 = u * v *)
  (* 使用 umul_split 的结果 *)
  rewrite Hsplit.
  
  (* 我们需要证明：
     w1 * 2^32 + w0 = x3 * 2^32 + (x1 + x2) * 2^16 + x0
  *)
  
  (* 关键步骤：展开 w1 和 w0，然后使用我们建立的引理 *)
  assert (Hw0_simpl: w0 = ((x1'' mod 2^16) * 2^16 + Z.land x0 65535) mod 2^32). {
    unfold w0.
    rewrite M32.
    rewrite Hshiftl.
    reflexivity.
  }
  
  assert (Hw1_simpl: w1 = ((x3 + 2^16) mod 2^32 + x1'' / 2^16) mod 2^32). {
    unfold w1.
    rewrite M32, M16.
    rewrite Hshiftr.
    reflexivity.
  }
  
  (* 分析 x3 + 2^16 的模运算 *)
  assert (Hx3_plus_mod: (x3 + 2^16) mod 2^32 = x3 + 2^16 - 2^32 \/ (x3 + 2^16) mod 2^32 = x3 + 2^16). {
    destruct (Z_lt_dec (x3 + 2^16) (2^32)).
    - right. rewrite Z.mod_small by lia. reflexivity.
    - left.
      assert (Hx3_lt: x3 + 2^16 < 2^33). {
        assert (x3 < 2^32) by lia.
        nia.
      }
      assert (Hdiv_eq: (x3 + 2^16) / 2^32 = 1). {
        assert (2^32 <= x3 + 2^16) by lia.
        assert (x3 + 2^16 < 2 * 2^32) by nia.
        pose proof (Z.div_lt_upper_bound (x3 + 2^16) (2^32) 2 ltac:(lia) ltac:(lia)).
        pose proof (Zdiv_le_lower_bound (x3 + 2^16) (2^32) 1 ltac:(lia) ltac:(lia)).
        lia.
      }
      rewrite Z.mod_eq by lia.
      rewrite Hdiv_eq. nia.
  }
  
  (* 分析 w0 的值 *)
  assert (Hw0_cases: w0 = (x1'' mod 2^16) * 2^16 + Z.land x0 65535 \/
                        w0 = (x1'' mod 2^16) * 2^16 + Z.land x0 65535 - 2^32). {
    rewrite Hw0_simpl.
    assert (Hmod_bound: x1'' mod 2^16 < 2^16). {
      apply Z.mod_pos_bound. lia.
    }
    assert (Hland_bound: Z.land x0 65535 < 2^16). {
      pose proof (land_65535_bounds x0 ltac:(rewrite M32; lia)) as Hlb.
      lia.
    }
    assert (Hbound: (x1'' mod 2^16) * 2^16 + Z.land x0 65535 < 2^33) by nia.
    assert (Hmod_nonneg: 0 <= x1'' mod 2^16) by (apply Z.mod_pos_bound; lia).
    assert (Hland_nonneg: 0 <= Z.land x0 65535) by (apply Z.land_nonneg; lia).
    destruct (Z_lt_dec ((x1'' mod 2^16) * 2^16 + Z.land x0 65535) (2^32)).
    - left. rewrite Z.mod_small by nia. reflexivity.
    - right.
      assert (Hdiv_eq: ((x1'' mod 2^16) * 2^16 + Z.land x0 65535) / 2^32 = 1). {
        assert (2^32 <= (x1'' mod 2^16) * 2^16 + Z.land x0 65535) by lia.
        assert ((x1'' mod 2^16) * 2^16 + Z.land x0 65535 < 2 * 2^32) by nia.
        pose proof (Z.div_lt_upper_bound ((x1'' mod 2^16) * 2^16 + Z.land x0 65535) (2^32) 2 ltac:(lia) ltac:(lia)).
        pose proof (Zdiv_le_lower_bound ((x1'' mod 2^16) * 2^16 + Z.land x0 65535) (2^32) 1 ltac:(lia) ltac:(lia)).
        lia.
      }
      rewrite Z.mod_eq by lia.
      rewrite Hdiv_eq. nia.
  }
  
  (* 分析 x1 + Z.shiftr x0 16 的进位情况 *)
  assert (Hx1'_carry_or_not: (x1 + Z.shiftr x0 16) / 2^32 = 0 \/ (x1 + Z.shiftr x0 16) / 2^32 = 1). {
    assert (Hx1_lt: x1 < 2^32) by lia.
    assert (Hshiftr_lt: Z.shiftr x0 16 < 2^16). {
      rewrite Z.shiftr_div_pow2 by lia.
      apply Z.div_lt_upper_bound; lia.
    }
    assert (Hsum_lt: x1 + Z.shiftr x0 16 < 2^32 + 2^16) by nia.
    assert (H2pow: 2^32 + 2^16 < 2 * 2^32) by nia.
    assert (Hdiv_lt: (x1 + Z.shiftr x0 16) / 2^32 < 2). {
      apply Z.div_lt_upper_bound; lia.
    }
    assert (Hshiftr_nonneg: 0 <= Z.shiftr x0 16) by (apply Z.shiftr_nonneg; lia).
    assert (Hdiv_nonneg: 0 <= (x1 + Z.shiftr x0 16) / 2^32) by (apply Z.div_pos; lia).
    lia.
  }
  
  assert (Hx1'_eq: x1' = (x1 + Z.shiftr x0 16) mod 2^32). {
    unfold x1'. rewrite M32. reflexivity.
  }
  
  assert (Hx1'_sum: x1 + Z.shiftr x0 16 = x1' \/ x1 + Z.shiftr x0 16 = x1' + 2^32). {
    rewrite Hx1'_eq.
    pose proof (Z_div_mod_eq_full (x1 + Z.shiftr x0 16) (2^32)) as Hdiv.
    destruct Hx1'_carry_or_not as [Hcase0 | Hcase1].
    - left. rewrite Hcase0 in Hdiv. nia.
    - right. rewrite Hcase1 in Hdiv. nia.
  }
  
  (* 现在分情况证明 *)
  destruct Hx1'_sum as [Hx1'_no_carry | Hx1'_carry].
  {
    (* 情况1：x1 + x0>>16 没有进位 *)
    assert (Hsum: x1' + x2 = x1'' + 2^32) by exact Hcarry.
    rewrite <- Hx1'_no_carry in Hsum.
    
    (* 关键：x1 + Z.shiftr x0 16 + x2 = x1'' + 2^32 *)
    (* 所以 x1 + x2 + Z.shiftr x0 16 = x1'' + 2^32 *)
    
    (* 目标是证明 w1 * 2^32 + w0 = u * v *)
    (* 其中 u * v = x3 * 2^32 + (x1 + x2) * 2^16 + x0 (由 Hsplit 给出) *)
    
    (* w1 = ((x3 + 2^16) mod 2^32 + x1'' / 2^16) mod 2^32 *)
    (* w0 = (x1'' mod 2^16 * 2^16 + Z.land x0 65535) mod 2^32 *)
    
    (* 由于 x1'' = x1 + Z.shiftr x0 16 + x2 - 2^32 *)
    (* x1'' / 2^16 = (x1 + Z.shiftr x0 16 + x2 - 2^32) / 2^16 *)
    (* x1'' mod 2^16 = (x1 + Z.shiftr x0 16 + x2 - 2^32) mod 2^16 *)
    
    assert (Hx1''_val: x1'' = x1 + Z.shiftr x0 16 + x2 - 2^32) by lia.
    
    (* 使用 Z.shiftr x0 16 = x0 / 2^16 *)
    assert (Hshiftr_x0: Z.shiftr x0 16 = x0 / 2^16) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    (* 使用 Z.land x0 65535 = x0 mod 2^16 *)
    assert (Hland_x0: Z.land x0 65535 = x0 mod 2^16). {
      assert (H65535_ones: 65535 = Z.ones 16) by reflexivity.
      rewrite H65535_ones. rewrite Z.land_ones by lia. reflexivity.
    }
    
    (* 重写 Hx1''_val 使用 x0 / 2^16 *)
    rewrite Hshiftr_x0 in Hx1''_val.
    
    (* 关键观察：
       x1'' = x1 + x0/2^16 + x2 - 2^32
       
       w1 * 2^32 + w0 应该等于 x3 * 2^32 + (x1 + x2) * 2^16 + x0
       
       让我们验证：
       w0 = (x1'' mod 2^16) * 2^16 + x0 mod 2^16  (如果没有溢出)
       w1 = (x3 + 2^16) mod 2^32 + x1'' / 2^16  (如果没有溢出)
       
       x1'' mod 2^16 = (x1 + x0/2^16 + x2 - 2^32) mod 2^16
                     = (x1 + x0/2^16 + x2) mod 2^16  (因为 2^32 是 2^16 的倍数)
       
       x1'' / 2^16 = (x1 + x0/2^16 + x2 - 2^32) / 2^16
                   = (x1 + x0/2^16 + x2) / 2^16 - 2^16
    *)
    
    (* 分解 x1 + x0/2^16 + x2 *)
    assert (Hx1_x2_sum_decomp: x1 + x0 / 2^16 + x2 = 
            ((x1 + x0 / 2^16 + x2) / 2^16) * 2^16 + (x1 + x0 / 2^16 + x2) mod 2^16). {
      pose proof (Z.div_mod (x1 + x0 / 2^16 + x2) (2^16) ltac:(lia)) as Hdm.
      lia.
    }
    
    (* x1'' mod 2^16 = (x1 + x0/2^16 + x2) mod 2^16 *)
    assert (Hx1''_mod: x1'' mod 2^16 = (x1 + x0 / 2^16 + x2) mod 2^16). {
      rewrite Hx1''_val.
      rewrite Zminus_mod.
      assert (2^32 mod 2^16 = 0). {
        assert (2^32 = 2^16 * 2^16) by (simpl; lia).
        rewrite H10. apply Z.mod_mul. lia.
      }
      rewrite H10. rewrite Z.sub_0_r.
      apply Z.mod_mod. lia.
    }
    
    (* x1'' / 2^16 = (x1 + x0/2^16 + x2) / 2^16 - 2^16 *)
    assert (Hx1''_div: x1'' / 2^16 = (x1 + x0 / 2^16 + x2) / 2^16 - 2^16). {
      rewrite Hx1''_val.
      (* (a - b) / c = a / c - b / c 当 b 是 c 的倍数时 *)
      assert (H2pow: 2^32 = 2^16 * 2^16) by (simpl; lia).
      (* 设 S = x1 + x0/2^16 + x2, 则 x1'' = S - 2^32 *)
      assert (Hsum_ge: x1 + x0 / 2^16 + x2 >= 2^32) by lia.
      
      (* 由于 S >= 2^32, 我们有 S / 2^16 >= 2^16 *)
      assert (Hsum_div_ge: (x1 + x0 / 2^16 + x2) / 2^16 >= 2^16). {
        assert (2^16 * 2^16 <= x1 + x0 / 2^16 + x2) by lia.
        pose proof (Z.div_le_mono (2^16 * 2^16) (x1 + x0 / 2^16 + x2) (2^16) ltac:(lia) H10).
        rewrite Z.div_mul in H11 by lia.
        lia.
      }
      
      (* 使用 Z.quot_rem 的性质 *)
      (* (S - 2^16 * 2^16) / 2^16 *)
      (* = ((S / 2^16) * 2^16 + S mod 2^16 - 2^16 * 2^16) / 2^16 *)
      (* = ((S / 2^16 - 2^16) * 2^16 + S mod 2^16) / 2^16 *)
      (* = S / 2^16 - 2^16  (因为 0 <= S mod 2^16 < 2^16) *)
      
      assert (Hmod_bound: 0 <= (x1 + x0 / 2^16 + x2) mod 2^16 < 2^16) by (apply Z.mod_pos_bound; lia).
      
      (* 直接用 Z.div_mod 和代数 *)
      pose proof (Z.div_mod (x1 + x0 / 2^16 + x2) (2^16) ltac:(lia)) as Hdm.
      pose proof (Z.div_mod (x1 + x0 / 2^16 + x2 - 2^16 * 2^16) (2^16) ltac:(lia)) as Hdm2.
      
      (* 验证 (S - 2^16*2^16) / 2^16 = S/2^16 - 2^16 *)
      assert (Hkey: (x1 + x0 / 2^16 + x2 - 2^16 * 2^16) / 2^16 = 
                    (x1 + x0 / 2^16 + x2) / 2^16 - 2^16). {
        remember ((x1 + x0 / 2^16 + x2) / 2^16) as q.
        remember ((x1 + x0 / 2^16 + x2) mod 2^16) as r.
        assert (Hqr: x1 + x0 / 2^16 + x2 = 2^16 * q + r) by lia.
        (* (2^16 * q + r - 2^16 * 2^16) / 2^16 = (q - 2^16) *)
        (* 因为 (q - 2^16) * 2^16 + r = 2^16 * q + r - 2^16 * 2^16 *)
        (* 且 0 <= r < 2^16 *)
        (* 使用 Z_div_mod_eq_full 的逆向 *)
        assert (Heq: x1 + x0 / 2^16 + x2 - 2^16 * 2^16 = 2^16 * (q - 2^16) + r) by lia.
        assert (Hmod_eq: (x1 + x0 / 2^16 + x2 - 2^16 * 2^16) mod 2^16 = r). {
          rewrite Heq.
          rewrite Z.add_mod by lia.
          assert (Hmul0: 2^16 * (q - 2^16) mod 2^16 = 0). {
            rewrite Z.mul_comm. apply Z.mod_mul. lia.
          }
          rewrite Hmul0. rewrite Z.add_0_l.
          rewrite Z.mod_mod by lia.
          apply Z.mod_small. exact Hmod_bound.
        }
        pose proof (Z_div_mod_eq_full (x1 + x0 / 2^16 + x2 - 2^16 * 2^16) (2^16)) as Hdiv.
        rewrite Hmod_eq in Hdiv.
        lia.
      }
      exact Hkey.
    }
    
    (* 设 S = x1 + x0/2^16 + x2 *)
    remember (x1 + x0 / 2^16 + x2) as S.
    
    (* 证明 u * v = (x3 + S/2^16) * 2^32 + (S mod 2^16) * 2^16 + x0 mod 2^16 *)
    assert (Huv_alt: u * v = (x3 + S / 2^16) * 2^32 + (S mod 2^16) * 2^16 + x0 mod 2^16). {
      assert (Hx0_decomp2: x0 = (x0 / 2^16) * 2^16 + x0 mod 2^16). {
        pose proof (Z.div_mod x0 (2^16) ltac:(lia)) as Hdm. lia.
      }
      assert (HS_decomp: S = (S / 2^16) * 2^16 + S mod 2^16). {
        pose proof (Z.div_mod S (2^16) ltac:(lia)) as Hdm. lia.
      }
      
      assert (Huv_form: u * v = x3 * 2^32 + (x1 + x2) * 2^16 + x0). {
        rewrite Hsplit.
        assert (Hland_eq: Z.land u (2^16 - 1) = ul) by (rewrite <- M15; symmetry; exact H1).
        assert (Hland_eq2: Z.land v (2^16 - 1) = vl) by (rewrite <- M15; symmetry; exact H3).
        rewrite Hland_eq, Hland_eq2, <- H2, <- H4, H5, H6, H7, H8. ring.
      }
      
      assert (HS_eq: x1 + x2 + x0 / 2^16 = S) by (rewrite HeqS; lia).
      
      rewrite Huv_form.
      remember (x0 / 2^16) as q0. remember (x0 mod 2^16) as r0.
      
      assert (Hstep1: (x1 + x2) * 2^16 + x0 = S * 2^16 + r0). {
        subst r0 q0.
        assert (Hsimp: (x1 + x2) * 2^16 + x0 = (x1 + x2 + x0 / 2^16) * 2^16 + x0 mod 2^16). {
          rewrite Hx0_decomp2 at 1. ring.
        }
        rewrite Hsimp, HS_eq. reflexivity.
      }
      
      assert (Hstep2: S * 2^16 = S / 2^16 * 2^32 + S mod 2^16 * 2^16). {
        assert (H2pow: 2^32 = 2^16 * 2^16) by reflexivity.
        rewrite H2pow, HS_decomp at 1. ring.
      }
      
      subst r0 q0.
      assert (Hleft: x3 * 2^32 + (x1 + x2) * 2^16 + x0 = x3 * 2^32 + (S * 2^16 + x0 mod 2^16)). {
        rewrite <- Hstep1. ring.
      }
      rewrite Hleft, Hstep2. ring.
    }
    
    (* 现在证明 w0 = (S mod 2^16) * 2^16 + x0 mod 2^16 *)
    assert (Hw0_val: w0 = (S mod 2^16) * 2^16 + x0 mod 2^16). {
      rewrite Hw0_simpl.
      rewrite Hx1''_mod.
      rewrite HeqS.
      rewrite Hland_x0.
      (* 证明 (S mod 2^16) * 2^16 + x0 mod 2^16 < 2^32 *)
      assert (Hmod_S_bound: 0 <= (x1 + x0 / 2^16 + x2) mod 2^16 < 2^16) by (apply Z.mod_pos_bound; lia).
      assert (Hmod_x0_bound: 0 <= x0 mod 2^16 < 2^16) by (apply Z.mod_pos_bound; lia).
      assert (Hsum_bound: (x1 + x0 / 2^16 + x2) mod 2^16 * 2^16 + x0 mod 2^16 < 2^32) by nia.
      assert (Hsum_nonneg: 0 <= (x1 + x0 / 2^16 + x2) mod 2^16 * 2^16 + x0 mod 2^16) by nia.
      apply Z.mod_small. lia.
    }
    
    (* 现在证明 w1 = (x3 + S / 2^16) mod 2^32 *)
    assert (Hw1_val: w1 = (x3 + S / 2^16) mod 2^32). {
      rewrite Hw1_simpl.
      rewrite Hx1''_div.
      rewrite HeqS.
      (* w1 = ((x3 + 2^16) mod 2^32 + (x1 + x0/2^16 + x2)/2^16 - 2^16) mod 2^32 *)
      (* 需要证明这等于 (x3 + (x1 + x0/2^16 + x2)/2^16) mod 2^32 *)
      
      (* 分情况：x3 + 2^16 < 2^32 或 x3 + 2^16 >= 2^32 *)
      destruct (Z_lt_dec (x3 + 2^16) (2^32)).
      {
        (* 情况1：x3 + 2^16 < 2^32 *)
        assert (Hx3_mod: (x3 + 2^16) mod 2^32 = x3 + 2^16) by (apply Z.mod_small; lia).
        rewrite Hx3_mod.
        (* 目标: (x3 + 2^16 + ((x1 + x0/2^16 + x2)/2^16 - 2^16)) mod 2^32 = (x3 + (x1 + x0/2^16 + x2)/2^16) mod 2^32 *)
        (* x3 + 2^16 + (S/2^16 - 2^16) = x3 + S/2^16 *)
        f_equal.
        lia.
      }
      {
        (* 情况2：x3 + 2^16 >= 2^32 *)
        assert (Hx3_mod: (x3 + 2^16) mod 2^32 = x3 + 2^16 - 2^32). {
          assert (Hlt: x3 + 2^16 < 2 * 2^32) by nia.
          assert (Hge: x3 + 2^16 >= 2^32) by lia.
          rewrite Z.mod_eq by lia.
          (* (x3 + 2^16) / 2^32 = 1 因为 2^32 <= x3 + 2^16 < 2 * 2^32 *)
          assert (Hdiv1: (x3 + 2^16) / 2^32 = 1). {
            (* 2^32 <= x3 + 2^16 < 2 * 2^32 意味着 (x3 + 2^16) / 2^32 = 1 *)
            (* 设 q = (x3 + 2^16) / 2^32, r = (x3 + 2^16) mod 2^32 *)
            set (q := (x3 + 2^16) / 2^32).
            set (r := (x3 + 2^16) mod 2^32).
            pose proof (Z.div_mod (x3 + 2^16) (2^32) ltac:(lia)) as Hdm.
            fold q r in Hdm.
            pose proof (Z.mod_pos_bound (x3 + 2^16) (2^32) ltac:(lia)) as Hmod_bound.
            fold r in Hmod_bound.
            (* x3 + 2^16 = 2^32 * q + r, 其中 0 <= r < 2^32 *)
            (* 由于 2^32 <= x3 + 2^16 < 2 * 2^32，q 必须是 1 *)
            assert (Hq_nonneg: q >= 0). {
              (* q = (x3 + 2^16) / 2^32, 由于 x3 + 2^16 >= 0 且 2^32 > 0，q >= 0 *)
              (* 由 Hdm: x3 + 2^16 = 2^32 * q + r 和 0 <= r < 2^32 *)
              (* 如果 q < 0，则 2^32 * q <= -2^32，所以 x3 + 2^16 <= -2^32 + r < 0 *)
              (* 但 x3 + 2^16 >= 2^32 > 0，矛盾 *)
              destruct (Z_lt_dec q 0).
              - assert (2^32 * q <= -2^32) by nia.
                lia.
              - lia.
            }
            assert (Hq_ge1: q >= 1). {
              destruct (Z_lt_dec q 1).
              - (* q < 1, 即 q = 0 *)
                assert (Hq0: q = 0) by lia.
                rewrite Hq0, Z.mul_0_r in Hdm. lia.
              - lia.
            }
            assert (Hq_lt2: q < 2). {
              destruct (Z_lt_dec q 2); auto.
              (* q >= 2 *)
              assert (Hq2: q >= 2) by lia.
              assert (2^32 * q >= 2^32 * 2) by nia.
              lia.
            }
            lia.
          }
          lia.
        }
        rewrite Hx3_mod.
        (* 目标: (x3 + 2^16 - 2^32 + ((x1 + x0/2^16 + x2)/2^16 - 2^16)) mod 2^32 = (x3 + (x1 + x0/2^16 + x2)/2^16) mod 2^32 *)
        (* x3 + 2^16 - 2^32 + (S/2^16 - 2^16) = x3 + S/2^16 - 2^32 *)
        (* 两边相差 2^32，所以 mod 2^32 后相等 *)
        assert (Heq: x3 + 2^16 - 2^32 + ((x1 + x0 / 2^16 + x2) / 2^16 - 2^16) = 
                     x3 + (x1 + x0 / 2^16 + x2) / 2^16 - 2^32) by lia.
        rewrite Heq.
        (* (a - 2^32) mod 2^32 = a mod 2^32 *)
        rewrite Zminus_mod.
        rewrite Z.mod_same by lia.
        rewrite Z.sub_0_r.
        apply Z.mod_mod. lia.
      }
    }
    
    (* 最终目标: w1 * 4294967296 + w0 = Hsplit展开后的形式 *)
    (* Hsplit 已经把目标中的 u * v 展开了 *)
    (* Huv_alt: u * v = (x3 + S/2^16) * 2^32 + S mod 2^16 * 2^16 + x0 mod 2^16 *)
    
    (* 策略：用 transitivity 通过 u * v *)
    transitivity (u * v).
    2: { exact Hsplit. }
    
    (* 现在目标: w1 * 4294967296 + w0 = u * v *)
    rewrite M32, Hw0_val, Hw1_val, Huv_alt.
    
    (* 目标: (x3 + S/2^16) mod 2^32 * 2^32 + S mod 2^16 * 2^16 + x0 mod 2^16 
           = (x3 + S/2^16) * 2^32 + S mod 2^16 * 2^16 + x0 mod 2^16 *)
    
    assert (HS_bound: S < 2^33 + 2^16). {
      rewrite HeqS.
      assert (x0 / 2^16 < 2^16) by (apply Z.div_lt_upper_bound; lia).
      lia.
    }
    assert (HS_div_bound: S / 2^16 < 2^17 + 1) by (apply Z.div_lt_upper_bound; lia).
    assert (Hsum_bound2: x3 + S / 2^16 < 2^33) by lia.
    
    destruct (Z_lt_dec (x3 + S / 2^16) (2^32)).
    - assert (Hmod_small: (x3 + S / 2^16) mod 2^32 = x3 + S / 2^16). {
        apply Z.mod_small.
        split.
        + assert (0 <= S / 2^16) by (apply Z.div_pos; lia). lia.
        + lia.
      }
      rewrite Hmod_small. lia.
    - exfalso.
      assert (Huv_bound: u * v < 2^64) by nia.
      rewrite Huv_alt in Huv_bound.
      pose proof (Z.mod_pos_bound S (2^16) ltac:(lia)).
      pose proof (Z.mod_pos_bound x0 (2^16) ltac:(lia)).
      nia.
  }
  {
    (* 情况2：x1 + x0>>16 有进位 *)
    (* Hx1'_carry: x1 + Z.shiftr x0 16 = x1' + 2^32 *)
    (* 这意味着 x1 + Z.shiftr x0 16 >= 2^32 *)
    
    (* 我们证明这种情况不可能发生 *)
    exfalso.
    
    (* x1' < 2^16 因为 x1 + Z.shiftr x0 16 < 2^32 + 2^16 *)
    assert (Hx1'_small: x1' < 2^16). {
      assert (Hshiftr_bound: Z.shiftr x0 16 < 2^16). {
        rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; lia.
      }
      lia.
    }
    
    (* x1' + x2 >= 2^32 因为 Hcarry: x1'' < x2 *)
    assert (Hsum_ge: x1' + x2 >= 2^32). {
      destruct (Z_lt_dec (x1' + x2) (2^32)).
      - assert (Hx1''_eq: x1'' = x1' + x2) by (unfold x1''; rewrite Z.mod_small; lia).
        lia.
      - lia.
    }
    
    (* 从 x1' + x2 >= 2^32 和 x1' < 2^16，得到 x2 > 2^32 - 2^16 *)
    assert (Hx2_large: x2 > 2^32 - 2^16) by lia.
    
    (* 从 Hx1'_carry: x1 + Z.shiftr x0 16 >= 2^32 *)
    (* 和 Z.shiftr x0 16 < 2^16，得到 x1 > 2^32 - 2^16 *)
    assert (Hshiftr_bound: Z.shiftr x0 16 < 2^16). {
      rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; lia.
    }
    assert (Hx1_large: x1 > 2^32 - 2^16) by lia.
    
    (* 但 x1 = ul * vh，其中 ul, vh < 2^16 *)
    (* 所以 x1 <= (2^16 - 1) * (2^16 - 1) = 2^32 - 2^17 + 1 < 2^32 - 2^16 *)
    (* 这与 Hx1_large 矛盾！ *)
    
    (* 使用已有的边界 Hx1_bounds: 0 <= x1 < 2^32 *)
    (* x1 = ul * vh，其中 ul < 2^16 且 vh < 2^16 *)
    (* 所以 x1 < 2^16 * 2^16 = 2^32 *)
    (* 更精确地，x1 <= (2^16 - 1) * (2^16 - 1) = 2^32 - 2^17 + 1 *)
    
    assert (Hul_bound: 0 <= ul < 2^16). {
      pose proof (land_65535_bounds u H) as Hb.
      rewrite <- H1 in Hb. exact Hb.
    }
    assert (Hvh_bound: 0 <= vh < 2^16). {
      pose proof (shiftr_16_bounds v H0) as Hb.
      rewrite <- H4 in Hb. exact Hb.
    }
    assert (Hx1_upper: x1 <= (2^16 - 1) * (2^16 - 1)). {
      rewrite H6. nia.
    }
    assert (H2pow: (2^16 - 1) * (2^16 - 1) = 2^32 - 2^17 + 1) by (compute; reflexivity).
    assert (Hx1_upper': x1 <= 2^32 - 2^17 + 1) by lia.
    assert (Hcontra: 2^32 - 2^17 + 1 < 2^32 - 2^16) by (compute; lia).
    lia.
  }
Qed.

Lemma umul_ppmm_correct_no_carry: forall u v ul uh vl vh x0 x1 x2 x3,
  0 <= u < 4294967296 ->
  0 <= v < 4294967296 ->
  ul = Z.land u 65535 ->
  uh = Z.shiftr u 16 ->
  vl = Z.land v 65535 ->
  vh = Z.shiftr v 16 ->
  x0 = ul * vl ->
  x1 = ul * vh ->
  x2 = uh * vl ->
  x3 = uh * vh ->
  let x1' := (x1 + Z.shiftr x0 16) mod 4294967296 in
  let x1'' := (x1' + x2) mod 4294967296 in
  x1'' >= x2 ->
  let w1 := (x3 + Z.shiftr x1'' 16) mod 4294967296 in
  let w0 := ((Z.shiftl x1'' 16) mod 4294967296 + Z.land x0 65535) mod 4294967296 in
  w1 * 4294967296 + w0 = u * v.
Proof.
  intros u v ul uh vl vh x0 x1 x2 x3.
  intros Hu Hv Hul Huh Hvl Hvh Hx0 Hx1 Hx2 Hx3 x1' x1'' Hnocarry w1 w0.
  
  (* 常量定义 *)
  assert (M: 4294967296 = 2^32) by reflexivity.
  assert (H: 65536 = 2^16) by reflexivity.
  assert (HM: 65535 = 2^16 - 1) by reflexivity.
  
  (* 边界条件 *)
  pose proof (land_65535_bounds u Hu) as [Hul_lb Hul_ub].
  pose proof (land_65535_bounds v Hv) as [Hvl_lb Hvl_ub].
  pose proof (shiftr_16_bounds u Hu) as [Huh_lb Huh_ub].
  pose proof (shiftr_16_bounds v Hv) as [Hvh_lb Hvh_ub].
  
  subst ul uh vl vh x0 x1 x2 x3.
  rewrite M, H, HM in *.
  
  (* 利用 umul_split 得到 u * v 的分解 *)
  pose proof (umul_split u v Hu Hv) as Hsplit.
  rewrite M, H in Hsplit.
  
  (* 简化 Hsplit *)
  set (ul := Z.land u (2^16 - 1)) in *.
  set (uh := Z.shiftr u 16) in *.
  set (vl := Z.land v (2^16 - 1)) in *.
  set (vh := Z.shiftr v 16) in *.
  
  (* 关键观察：x1'' >= x2 意味着无进位 *)
  (* 即 x1' + x2 < 2^32 *)
  assert (Heq65535: 65535 = 2^16 - 1) by reflexivity.
  assert (Hvl_eq: vl = Z.land v 65535).
  { unfold vl. rewrite Heq65535. reflexivity. }
  assert (Hul_eq: ul = Z.land u 65535).
  { unfold ul. rewrite Heq65535. reflexivity. }
  assert (Hx1''_def: x1' + (uh * vl) = x1'').
  { unfold x1''. rewrite Hvl_eq.
    apply Z_mod_add_uncarry.
    + lia.
    + apply Z.mod_pos_bound. lia.
    + nia.
    + rewrite <- Hvl_eq. assumption. }
  
  (* 分析 w0 的构造 *)
  (* w0 = (x1'' << 16) mod 2^32 + (x0 & 0xFFFF) mod 2^32 *)
  assert (Hw0_simp: w0 = (x1'' mod 2^16) * 2^16 + ul * vl mod 2^16).
  {
    unfold w0.
    (* 应用 shiftl_16_mod_low: (Z.shiftl x 16) mod 4294967296 = ((x mod 65536) * 65536) mod 4294967296 *)
    rewrite shiftl_16_mod_low by (apply Z.mod_pos_bound; lia).
    (* 目标现在是: ((x1'' mod 65536 * 65536) mod 4294967296 + Z.land (...) 65535) mod 4294967296 = RHS *)
    
    assert (Hx1''_bound: 0 <= x1'' < 2^32).
    { split. apply Z.mod_pos_bound. lia. apply Z.mod_pos_bound. lia. }
    
    (* 先证明 ul * vl 的界限 *)
    assert (Hul_vl_bound: 0 <= ul * vl < 2^32).
    { split. nia. assert (ul < 2^16) by lia. assert (vl < 2^16) by lia. nia. }
    
    (* 简化 Z.land 部分：先处理这个，然后再统一常数 *)
    (* 证明：Z.land (Z.land u 65535 * Z.land v 65535) 65535 = (Z.land u 65535 * Z.land v 65535) mod 2^16 *)
    assert (Hland_direct: Z.land (Z.land u 65535 * Z.land v 65535) 65535 = 
                          (Z.land u 65535 * Z.land v 65535) mod 2^16).
    { assert (Hones: 65535 = Z.ones 16) by reflexivity.
      rewrite Hones. apply Z.land_ones.
      assert (Hprod_bound: 0 <= Z.land u 65535 * Z.land v 65535).
      { assert (0 <= Z.land u 65535) by (apply Z.land_nonneg; lia).
        assert (0 <= Z.land v 65535) by (apply Z.land_nonneg; lia).
        nia. }
      lia. }
    
    (* 在目标中用 Hland_direct 替换 *)
    rewrite Hland_direct.
    (* 目标现在是: ((x1'' mod 65536 * 65536) mod 4294967296 + (Z.land u 65535 * Z.land v 65535) mod 2^16) mod 4294967296 = RHS *)
    
    (* 统一常数：把数字形式转换为幂次形式 *)
    rewrite M, H. (* 4294967296 = 2^32, 65536 = 2^16 *)
    (* 目标现在是: ((x1'' mod 2^16 * 2^16) mod 2^32 + (Z.land u 65535 * Z.land v 65535) mod 2^16) mod 2^32 = RHS *)
    
    (* 现在用 Hul_eq 和 Hvl_eq 重写右边的表达式，使其与左边统一 *)
    (* 右边的 RHS 是: (x1'' mod 2^16) * 2^16 + ul * vl mod 2^16 *)
    (* 目标左边有: (Z.land u 65535 * Z.land v 65535) mod 2^16 *)
    (* 我们需要证明这等于 (ul * vl) mod 2^16 *)
    
    (* 先用 ul 和 vl 的定义重写右边 *)
    rewrite Hul_eq, Hvl_eq.
    (* 现在 RHS 变成: (x1'' mod 2^16) * 2^16 + (Z.land u 65535 * Z.land v 65535) mod 2^16 *)
    
    (* 第一步：简化内层的 (x1'' mod 2^16 * 2^16) mod 2^32 *)
    (* 我们需要证明 x1'' mod 2^16 * 2^16 < 2^32，因此 mod 可以消除 *)
    assert (Hinner: (x1'' mod 2^16 * 2^16) mod 2^32 = x1'' mod 2^16 * 2^16).
    { apply Z.mod_small. split.
      - (* 下界 *)
        pose proof (Z.mod_pos_bound x1'' (2^16)) as Hmod.
        assert (0 < 2^16) by lia. specialize (Hmod H0). lia.
      - (* 上界 *)
        pose proof (Z.mod_pos_bound x1'' (2^16)) as Hmod.
        assert (0 < 2^16) by lia. specialize (Hmod H0).
        assert (Heq: 2^16 * 2^16 = 2^32) by (compute; reflexivity).
        lia. }
    rewrite Hinner.
    (* 目标现在是: (x1'' mod 2^16 * 2^16 + (Z.land u 65535 * Z.land v 65535) mod 2^16) mod 2^32 
                  = (x1'' mod 2^16) * 2^16 + (Z.land u 65535 * Z.land v 65535) mod 2^16 *)
    
    (* 第二步：简化外层的 mod *)
    (* 证明一个关于外层 mod 的断言，然后用它重写 *)
    assert (Houter: (x1'' mod 2^16 * 2^16 + (Z.land u 65535 * Z.land v 65535) mod 2^16) mod 2^32 =
                    x1'' mod 2^16 * 2^16 + (Z.land u 65535 * Z.land v 65535) mod 2^16).
    { apply Z.mod_small. split.
      - (* 下界 *)
        pose proof (Z.mod_pos_bound x1'' (2^16)) as Hmod1.
        pose proof (Z.mod_pos_bound (Z.land u 65535 * Z.land v 65535) (2^16)) as Hmod2.
        assert (0 < 2^16) by lia.
        specialize (Hmod1 H0). specialize (Hmod2 H0).
        lia.
      - (* 上界 *)
        pose proof (Z.mod_pos_bound x1'' (2^16)) as Hmod1.
        pose proof (Z.mod_pos_bound (Z.land u 65535 * Z.land v 65535) (2^16)) as Hmod2.
        assert (0 < 2^16) by lia.
        specialize (Hmod1 H0). specialize (Hmod2 H0).
        assert (Heq: 2^16 * 2^16 = 2^32) by (compute; reflexivity).
        (* x1'' mod 2^16 < 2^16，所以 x1'' mod 2^16 * 2^16 < 2^16 * 2^16 = 2^32 *)
        (* (Z.land u 65535 * Z.land v 65535) mod 2^16 < 2^16 *)
        (* 但我们需要证明两者之和 < 2^32，这需要更精确的界 *)
        (* x1'' mod 2^16 * 2^16 最大是 (2^16 - 1) * 2^16 = 2^32 - 2^16 *)
        (* (...) mod 2^16 最大是 2^16 - 1 *)
        (* 所以和最大是 2^32 - 2^16 + 2^16 - 1 = 2^32 - 1 < 2^32 *)
        assert (Hbound1: x1'' mod 2^16 <= 2^16 - 1).
        { assert (x1'' mod 2^16 < 2^16) by lia.
          lia. }
        assert (Hbound2: x1'' mod 2^16 * 2^16 <= (2^16 - 1) * 2^16).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        assert (Heq2: (2^16 - 1) * 2^16 = 2^32 - 2^16) by (compute; reflexivity).
        lia. }
    rewrite Houter.
    reflexivity.
  }
  
  (* 分析 w1 的构造 *)
  assert (Hw1_simp: w1 = (uh * vh + x1'' / 2^16) mod 2^32).
  {
    unfold w1.
    rewrite Z.shiftr_div_pow2 by lia.
    reflexivity.
  }
  
  (* 核心证明：w1 * 2^32 + w0 = u * v *)
  rewrite Hw0_simp, Hw1_simp.
  
  (* 利用 x1'' = (x1'' / 2^16) * 2^16 + x1'' mod 2^16 *)
  pose proof (decompose_by_shift x1'' (2^16) ltac:(lia) ltac:(apply Z.mod_pos_bound; lia)) as Hx1''_decomp.
  
  (* w1 * 2^32 + w0 = ... *)
  (* 先简化目标，利用 w1, w0 的定义和无进位性质 *)
  (* 目标应该形如: (uh * vh + x1'' / 2^16) mod 2^32 * 2^32 + ... = u * v *)
  (* 关键：由于无进位，(uh * vh + x1'' / 2^16) < 2^32，因此 mod 可以去掉 *)
  
  assert (Hno_carry: uh * vh + x1'' / 2^16 < 2^32).
  {
    (* 关键：利用无进位条件 x1'' >= x2 和各部分的界限 *)
    (* 首先，uh * vh < 2^32 因为 uh, vh < 2^16 *)
    assert (Huh_vh_bound: uh * vh < 2^32).
    { assert (uh < 2^16) by lia.
      assert (vh < 2^16) by lia.
      assert (2^16 * 2^16 = 2^32) by (compute; reflexivity).
      nia. }
    
    (* x1'' < 2^32 因为它是 mod 2^32 的结果 *)
    assert (Hx1''_bound: 0 <= x1'' < 2^32).
    { unfold x1''. apply Z.mod_pos_bound. lia. }
    
    (* x1'' / 2^16 < 2^16 *)
    assert (Hx1''_div_bound: x1'' / 2^16 < 2^16).
    { apply Z.div_lt_upper_bound; lia. }
    
    (* 因此 uh * vh + x1'' / 2^16 < 2^32 + 2^16 *)
    (* 但我们需要更精确的界限 *)
    (* 关键观察：从无进位条件 x1'' >= x2 和 x1'' = (x1' + x2) mod 2^32 *)
    (* 可知 x1' + x2 < 2^32（无进位） *)
    (* 因此 x1'' = x1' + x2 *)
    
    (* 从 Hx1''_def: x1' + uh * vl = x1'' 和无进位条件 *)
    (* 我们知道 x1' + uh * vl < 2^32 *)
    assert (Hx1'_x2_bound: x1' + uh * vl < 2^32).
    { (* 利用 Hx1''_def: x1' + uh * vl = x1'' *)
      (* 和 Hnocarry: x1'' >= uh * vl *)
      rewrite Hvl_eq in Hnocarry.
      assert (Hx1'_bound: 0 <= x1' < 2^32).
      { unfold x1'. apply Z.mod_pos_bound. lia. }
      assert (Hx2_bound: 0 <= uh * vl < 2^32).
      { split. nia.
        assert (uh < 2^16) by lia.
        assert (vl < 2^16) by lia.
        nia. }
      (* x1'' = (x1' + uh * vl) mod 2^32 *)
      (* 如果 x1' + uh * vl >= 2^32，则 (x1' + uh * vl) mod 2^32 < uh * vl *)
      (* 但 Hnocarry 说 x1'' >= uh * vl，矛盾 *)
      destruct (Z_lt_dec (x1' + uh * vl) (2^32)).
      - assumption.
      - (* x1' + uh * vl >= 2^32 的情况 *)
        unfold x1'' in Hnocarry.
        assert (Hcarry_case: (x1' + uh * vl) mod 2^32 < uh * vl).
        { apply Z_mod_add_carry_condition; lia. }
        lia. }
    
    (* 现在利用 x1' 的定义和界限 *)
    (* x1' = (ul * vh + (ul * vl) / 2^16) mod 2^32 *)
    (* 且 x1' + uh * vl < 2^32 *)
    (* 因此 x1' < 2^32 - uh * vl *)
    
    (* x1'' = x1' + uh * vl < 2^32 *)
    (* 所以 x1'' / 2^16 <= (2^32 - 1) / 2^16 = 2^16 - 1 *)
    assert (Hx1''_div_precise: x1'' / 2^16 <= 2^16 - 1).
    { (* 从 Hx1''_def: x1' + uh * vl = x1'' 和 Hx1'_x2_bound: x1' + uh * vl < 2^32 *)
      (* 可得 x1'' < 2^32 *)
      assert (Hx1''_lt: x1'' < 2^32).
      { rewrite <- Hx1''_def. apply Hx1'_x2_bound. }
      (* 因此 x1'' / 2^16 < 2^32 / 2^16 = 2^16 *)
      assert (x1'' / 2^16 < 2^16).
      { apply Z.div_lt_upper_bound; lia. }
      lia. }
    
    (* 因此 uh * vh + x1'' / 2^16 <= uh * vh + 2^16 - 1 < 2^32 *)
    (* 因为 uh * vh < 2^32 且 uh, vh < 2^16 意味着 uh * vh <= (2^16-1)^2 < 2^32 - 2^16 *)
    assert (Huh_vh_precise: uh * vh <= (2^16 - 1) * (2^16 - 1)).
    { assert (uh <= 2^16 - 1) by lia.
      assert (vh <= 2^16 - 1) by lia.
      apply Z.mul_le_mono_nonneg; lia. }
    
    assert (Heq: (2^16 - 1) * (2^16 - 1) = 2^32 - 2^17 + 1) by (compute; reflexivity).
    lia.
  }
  
  assert (Hno_carry_bound: 0 <= uh * vh + x1'' / 2^16 < 2^32).
  {
    split.
    - apply Z.add_nonneg_nonneg; try lia.
      apply Z.div_pos; lia.
    - apply Hno_carry.
  }
  
  rewrite Z.mod_small by apply Hno_carry_bound.
  
  (* 现在目标是：(uh * vh + x1'' / 2^16) * 2^32 + (x1'' mod 2^16) * 2^16 + ul * vl mod 2^16 = u * v *)
  
  (* 策略：直接展开 x1'' 并利用 Hsplit *)
  
  (* 展开 x1'' = x1' + uh * vl *)
  rewrite <- Hx1''_def.
  
  (* 现在目标是：(uh * vh + (x1' + uh * vl) / 2^16) * 2^32 + ((x1' + uh * vl) mod 2^16) * 2^16 + ul * vl mod 2^16 = u * v *)
  
  (* 展开 x1' *)
  assert (Hx1'_simp: x1' = ul * vh + (ul * vl) / 2^16).
  {
    unfold x1'.
    assert (Hx1'_bound: ul * vh + (ul * vl) / 2^16 < 2^32).
    { assert (ul < 2^16) by lia.
      assert (vh < 2^16) by lia.
      assert (vl < 2^16) by lia.
      assert (ul * vh < 2^32) by nia.
      assert (ul * vl < 2^32) by nia.
      assert ((ul * vl) / 2^16 < 2^16) by (apply Z.div_lt_upper_bound; lia).
      nia.
    }
    assert (Hx1'_bounds: 0 <= ul * vh + (ul * vl) / 2^16 < 2^32).
    {
      split.
      - apply Z.add_nonneg_nonneg; try nia.
        apply Z.div_pos; lia.
      - apply Hx1'_bound.
    }
    rewrite Hul_eq, Hvl_eq.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.mod_small by apply Hx1'_bounds.
    reflexivity.
  }
  
  rewrite Hx1'_simp.
  
  (* 现在目标是：(uh * vh + (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16) * 2^32 + ((ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16 + ul * vl mod 2^16 = u * v *)
  
  (* 关键：从 Hx1'_x2_bound 我们知道 ul * vh + ul * vl / 2^16 + uh * vl < 2^32 *)
  (* 因此可以使用 decompose_by_shift *)
  
  assert (Hsum_bound: 0 <= ul * vh + ul * vl / 2^16 + uh * vl < 2^32).
  { split.
    - assert (0 <= ul * vh) by nia.
      assert (0 <= ul * vl / 2^16) by (apply Z.div_pos; lia).
      assert (0 <= uh * vl) by nia.
      lia.
    - (* Recalcular o limite usando Hx1''_def e Hnocarry *)
      (* x1'' = x1' + uh * vl e x1'' >= uh * vl (sem carry) *)
      (* Portanto x1' + uh * vl < 2^32 *)
      rewrite Hvl_eq in Hnocarry.
      assert (Hx1'_bound: 0 <= x1' < 2^32).
      { unfold x1'. apply Z.mod_pos_bound. lia. }
      assert (Hx2_bound: 0 <= uh * vl < 2^32).
      { split. nia.
        assert (uh < 2^16) by lia.
        assert (vl < 2^16) by lia.
        nia. }
      (* Se x1' + uh * vl >= 2^32, então (x1' + uh * vl) mod 2^32 < uh * vl *)
      (* Mas Hnocarry diz x1'' >= uh * vl, contradição *)
      destruct (Z_lt_dec (x1' + uh * vl) (2^32)).
      + (* x1' + uh * vl < 2^32 *)
        rewrite <- Hx1'_simp. assumption.
      + (* x1' + uh * vl >= 2^32 - contradição *)
        unfold x1'' in Hnocarry.
        assert (Hcarry_case: (x1' + uh * vl) mod 2^32 < uh * vl).
        { apply Z_mod_add_carry_condition; lia. }
        (* Hnocarry: (x1' + uh * vl) mod 2^32 >= uh * vl *)
        (* Hcarry_case: (x1' + uh * vl) mod 2^32 < uh * vl *)
        (* Contradição *)
        assert (Hcontra: (x1' + uh * vl) mod 2^32 >= uh * vl /\ (x1' + uh * vl) mod 2^32 < uh * vl).
        { split; assumption. }
        lia. }
  
  (* 最终的代数证明 *)
  (* 目标：(uh * vh + (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16) * 2^32 + 
           ((ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16 + 
           ul * vl mod 2^16 = u * v *)
  
  (* 策略：利用 Hsplit 和 Hsum_bound 来简化 *)
  (* Hsplit: u * v = uh * vh * 2^32 + (uh * vl + ul * vh) * 2^16 + ul * vl *)
  
  (* 由于 ul * vh + ul * vl / 2^16 + uh * vl < 2^32，我们可以去掉 mod *)
  assert (Hsum_no_overflow: ul * vh + ul * vl / 2^16 + uh * vl < 2^32).
  { apply Hsum_bound. }
  
  (* 使用 decompose_by_shift 分解这个和 *)
  pose proof (decompose_by_shift (ul * vh + ul * vl / 2^16 + uh * vl) (2^16) ltac:(lia) ltac:(lia)) as Hsum_decomp.
  
  (* 同样分解 ul * vl *)
  pose proof (decompose_by_shift (ul * vl) (2^16) ltac:(lia) ltac:(nia)) as Hvl_decomp.
  
  (* 关键：直接证明目标等于 u * v *)
  (* 我们将通过代数变换来证明 *)
  
  (* 目标：(uh * vh + (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16) * 2^32 + 
           ((ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16 + 
           ul * vl mod 2^16 = u * v *)
  
  (* 利用 Hsum_decomp 重写第一部分 *)
  rewrite Hsum_decomp.
  
  (* 现在目标变成：
     (uh * vh + ((ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) / 2^16) * 2^32 + 
     (((ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) mod 2^16) * 2^16 + 
     ul * vl mod 2^16 = u * v
  *)
  
  (* 简化：由于 (ul * vh + ul * vl / 2^16 + uh * vl) < 2^32，
     我们有 (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16 = ul * vh + ul * vl / 2^16 + uh * vl *)
  
  (* 计算 ((ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) / 2^16 *)
  assert (Hdiv_simp: ((ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) / 2^16 = 
                     (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16).
  { rewrite <- Hsum_decomp. reflexivity. }
  
  rewrite Hdiv_simp. clear Hdiv_simp.
  
  (* 计算 ((ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) mod 2^16 *)
  assert (Hmod_simp: ((ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) mod 2^16 = 
                     (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16).
  { rewrite <- Hsum_decomp. reflexivity. }
  
  rewrite Hmod_simp. clear Hmod_simp.
  
  (* 现在目标是：
     (uh * vh + (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16) * 2^32 + 
     (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16
     
     因此：
     (ul * vh + ul * vl / 2^16 + uh * vl) * 2^16 = 
     ((ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16 = 
     (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 * 2^16 + (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16 * 2^16
  *)
  
  (* 关键：使用 f_equal 来分离等式的各个部分 *)
  (* 目标：uh * vh * 2^32 + (uh * vl + ul * vh) * 2^16 + ul * vl / 2^16 * 2^16 + ul * vl mod 2^16 = 
           uh * vh * 2^32 + (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 * 2^16 + 
                           ((ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16 + 
                           ul * vl mod 2^16 *)
  
  (* 消去两边相同的 uh * vh * 2^32 和 ul * vl mod 2^16 *)
  (* 只需证明：(uh * vl + ul * vh) * 2^16 + ul * vl / 2^16 * 2^16 = 
               (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 * 2^16 + 
               ((ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16 *)
  
  assert (Hmid_eq: (uh * vl + ul * vh) * 2^16 + ul * vl / 2^16 * 2^16 = 
                   (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 * 2^16 + 
                   ((ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16).
  { (* 从 Hsum_decomp 我们知道：
       ul * vh + ul * vl / 2^16 + uh * vl = 
       (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + 
       (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16 *)
    
    (* 两边乘以 2^16 *)
    assert (Hmul16: (ul * vh + ul * vl / 2^16 + uh * vl) * 2^16 = 
                    ((ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + 
                     (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16).
    { (* 直接从 Hsum_decomp 得出 *)
      assert (Htmp: ul * vh + ul * vl / 2^16 + uh * vl = 
                    (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + 
                    (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16).
      { exact Hsum_decomp. }
      (* 两边乘以 2^16 *)
      assert (Heq: (ul * vh + ul * vl / 2^16 + uh * vl) * 2^16 = 
                   ((ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + 
                    (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16).
      { rewrite <- Htmp. reflexivity. }
      exact Heq. }
    
    (* 展开右边 *)
    assert (Hexp_rhs: ((ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 + 
                       (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16 = 
                      (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 * 2^16 + 
                      (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16 * 2^16).
    { ring. }
    
    rewrite Hexp_rhs in Hmul16.
    
    (* 展开左边：(ul * vh + ul * vl / 2^16 + uh * vl) * 2^16 *)
    assert (Hexp_lhs: (ul * vh + ul * vl / 2^16 + uh * vl) * 2^16 = 
                      ul * vh * 2^16 + ul * vl / 2^16 * 2^16 + uh * vl * 2^16).
    { ring. }
    
    rewrite Hexp_lhs in Hmul16.
    
    (* 现在 Hmul16 是：
       ul * vh * 2^16 + ul * vl / 2^16 * 2^16 + uh * vl * 2^16 = 
       (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 * 2^16 + 
       (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16 * 2^16 *)
    
    (* 目标是证明：
       (uh * vl + ul * vh) * 2^16 + ul * vl / 2^16 * 2^16 = 
       (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 * 2^16 + 
       (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16 * 2^16 *)
    
    (* 展开左边 *)
    assert (Hexp_goal_lhs: (uh * vl + ul * vh) * 2^16 + ul * vl / 2^16 * 2^16 = 
                           uh * vl * 2^16 + ul * vh * 2^16 + ul * vl / 2^16 * 2^16).
    { ring. }
    
    rewrite Hexp_goal_lhs.
    
    (* 现在需要证明：
       uh * vl * 2^16 + ul * vh * 2^16 + ul * vl / 2^16 * 2^16 = 
       (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 * 2^16 + 
       (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16 * 2^16 *)
    
    (* 从 Hmul16 我们知道：
       ul * vh * 2^16 + ul * vl / 2^16 * 2^16 + uh * vl * 2^16 = 
       (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16 * 2^16 * 2^16 + 
       (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16 * 2^16 *)
    
    (* 这两个表达式只是项的顺序不同，它们相等 *)
    (* 左边：uh * vl * 2^16 + ul * vh * 2^16 + ul * vl / 2^16 * 2^16 *)
    (* 右边（Hmul16 的左边）：ul * vh * 2^16 + ul * vl / 2^16 * 2^16 + uh * vl * 2^16 *)
    
    (* 直接使用 Hmul16 的等式 *)
    transitivity (ul * vh * 2^16 + ul * vl / 2^16 * 2^16 + uh * vl * 2^16).
    - (* 证明左边等于中间值 *)
      ring.
    - (* 证明中间值等于右边 *)
      exact Hmul16. }
  
  (* 使用公理来完成最终的算术等式证明 *)
  (* 当前目标：(uh * vh + (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16) * 2^32 + 
               ((ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16) * 2^16 + 
               ul * vl mod 2^16 = u * v *)
  
  (* 需要提供的参数：
     - uh = Z.shiftr u 16 (由 set 定义)
     - vh = Z.shiftr v 16 (由 set 定义)
     - ul = Z.land u 65535 (由 Hul_eq)
     - vl = Z.land v 65535 (由 Hvl_eq)
     - 0 <= u < 2^32 (由 Hu)
     - 0 <= v < 2^32 (由 Hv)
     - ul * vh + ul * vl / 2^16 + uh * vl < 2^32 (由 Hsum_bound)
  *)
  
  (* 新策略：直接从当前简化的目标出发，使用 Hsplit 和代数性质 *)
  (* 当前目标：(uh * vh + (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16) * 2^32 + 
               (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16 * 2^16 + 
               ul * vl mod 2^16 = u * v *)
  
  (* 从 Hsplit 开始 *)
  rewrite <- Hul_eq, <- Hvl_eq in Hsplit.
  rewrite Hsplit.
  
  (* 现在需要证明：
     uh * vh * 2^32 + (uh * vl + ul * vh) * 2^16 + ul * vl = 
     (uh * vh + (ul * vh + ul * vl / 2^16 + uh * vl) / 2^16) * 2^32 + 
     (ul * vh + ul * vl / 2^16 + uh * vl) mod 2^16 * 2^16 + ul * vl mod 2^16 *)
  
  (* 关键：利用 Hsum_bound 这个条件 *)
  (* ul * vh + ul * vl / 2^16 + uh * vl < 2^32 *)
  (* 这意味着我们可以使用 Z.mod_small 和 decompose_by_shift *)
  
  (* 设 S = ul * vh + ul * vl / 2^16 + uh * vl *)
  set (S := ul * vh + ul * vl / 2^16 + uh * vl).
  
  (* 证明 S 的分解 *)
  assert (HS_decomp: S = S / 2^16 * 2^16 + S mod 2^16).
  { apply decompose_by_shift; lia. }
  
  (* 证明 ul * vl 的分解 *)
  assert (Hvl_decomp2: ul * vl = ul * vl / 2^16 * 2^16 + ul * vl mod 2^16).
  { apply decompose_by_shift; lia. }
  
  (* 关键：S * 2^16 = S / 2^16 * 2^32 + S mod 2^16 * 2^16 *)
  assert (HS_mul: S * 2^16 = S / 2^16 * 2^32 + S mod 2^16 * 2^16).
  { 
    assert (H2pow: 2^32 = 2^16 * 2^16) by reflexivity.
    rewrite HS_decomp at 1.
    rewrite H2pow.
    ring.
  }
  
  (* 证明 (uh * vl + ul * vh) * 2^16 + ul * vl / 2^16 * 2^16 = S * 2^16 *)
  assert (Hmid: (uh * vl + ul * vh) * 2^16 + ul * vl / 2^16 * 2^16 = S * 2^16).
  { unfold S. ring. }
  
  (* 现在完成主证明 *)
  (* 设变量来代替除法和模运算 *)
  set (P_div := ul * vl / 2^16).
  set (P_mod := ul * vl mod 2^16).
  set (S_div := S / 2^16).
  set (S_mod := S mod 2^16).
  
  (* 重写 Hvl_decomp2 和其他等式 *)
  assert (Hvl_decomp3: ul * vl = P_div * 2^16 + P_mod) by (unfold P_div, P_mod; exact Hvl_decomp2).
  assert (HS_decomp2: S = S_div * 2^16 + S_mod) by (unfold S_div, S_mod; exact HS_decomp).
  assert (HS_mul2: S * 2^16 = S_div * 2^32 + S_mod * 2^16).
  { unfold S_div, S_mod. exact HS_mul. }
  assert (Hmid2: (uh * vl + ul * vh) * 2^16 + P_div * 2^16 = S * 2^16).
  { unfold P_div, S. ring. }
  
  (* 证明左边等于右边 *)
  assert (Hlhs: uh * vh * 2^32 + (uh * vl + ul * vh) * 2^16 + ul * vl = 
                uh * vh * 2^32 + S * 2^16 + P_mod).
  { rewrite Hvl_decomp3. rewrite <- Hmid2. ring. }
  
  rewrite Hlhs.
  rewrite HS_mul2.
  unfold S_div, S_mod, S.
  ring.
Qed.

End Aux.