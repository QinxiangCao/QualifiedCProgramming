Require Import Coq.ZArith.ZArith.
From compcert.lib Require Import Coqlib Integers.
Local Open Scope Z.

Notation "'INT_MIN'" := (-2147483648).
Notation "'INT_MAX'" := (2147483647).
Notation "'UINT_MAX'" := (4294967295).
Notation "'INT64_MIN'" := (-9223372036854775808).
Notation "'INT64_MAX'" := (9223372036854775807).
Notation "'UINT64_MAX'" := (18446744073709551615).
Notation "'Zabs'" := (Z.abs).
Notation "'Zgcd'" := (Z.gcd).
Notation "x % y" := (Z.rem x y) (at level 40).

Definition unsigned_last_nbits (x : Z) (n : Z) : Z := 
   x mod (2 ^ n).
 
Definition signed_last_nbits (x : Z) (n : Z) : Z := 
   let v := x mod (2 ^ n) in 
   if (zlt v (2 ^ (n - 1))) then v else v - 2 ^ n.

Module Int128.
  Definition min_signed : Z := - 2 ^ 127.
  Definition max_signed : Z := 2 ^ 127 - 1.
  Definition max_unsigned : Z := 2 ^ 128 - 1.
End Int128.

Lemma Zland_land : forall x y c, Z.land (Z.land x y) c = Z.land (Z.land x c) (Z.land y c).
Proof.
  intros.
  rewrite (Z.land_assoc (Z.land x c)) at 1.
  rewrite (Z.land_comm x c).
  rewrite <- (Z.land_assoc c x y).
  rewrite (Z.land_comm c (Z.land x y)).
  rewrite <- (Z.land_assoc (Z.land x y) _ c).
  rewrite Z.land_diag.
  reflexivity.
Qed.

Lemma Byte_cast_correct : forall x, Byte.eqm x (unsigned_last_nbits x 8).
Proof.
  intros.
  unfold Byte.eqm, unsigned_last_nbits. 
  unfold Zbits.eqmod. exists (x / 2 ^ 8).
  rewrite (Z_div_mod_eq_full x (2^8)) at 1; try lia.
  rewrite Z.mul_comm.
  reflexivity.
Qed.

Lemma UByte_cast_correct : forall x, Byte.eqm x (signed_last_nbits x 8).
Proof.
  intros.
  unfold Byte.eqm, signed_last_nbits.
  unfold Zbits.eqmod. 
  destruct (zlt (x mod 2 ^ 8) (2 ^ (8 - 1))).
  - exists (x / 2 ^ 8).
    rewrite (Z_div_mod_eq_full x (2^8)) at 1; try lia.
    rewrite Z.mul_comm.
    reflexivity.
  - exists (x / 2 ^ 8 + 1).
    rewrite (Z_div_mod_eq_full x (2^8)) at 1; try lia.
    rewrite Z.mul_comm.
    rewrite Z.mul_add_distr_r.
    replace Byte.modulus with (2 ^ 8) by reflexivity.
    lia. 
Qed.

Lemma Int_cast_correct : forall x, Int.min_signed <= x <= Int.max_signed -> Int.cast_unsigned x = unsigned_last_nbits x 32.
Proof.
  intros. reflexivity.
Qed.

Lemma UInt_cast_correct : forall x, 0 <= x <= Int.max_unsigned -> Int.cast_signed x = signed_last_nbits x 32.
Proof. 
  intros.
  reflexivity.
Qed.

Lemma Int64_cast_correct : forall x, Int64.min_signed <= x <= Int64.max_signed -> Int64.cast_unsigned x = unsigned_last_nbits x 64.
Proof. 
  intros.
  reflexivity.
Qed. 

Lemma UInt64_cast_correct : forall x, 0 <= x <= Int64.max_unsigned -> Int64.cast_signed x = signed_last_nbits x 64.
Proof.
  intros.
  reflexivity.
Qed.

Lemma unsigned_Lastnbits_mod_correct : forall x n, n > 0 -> x mod 2 ^ n = (unsigned_last_nbits x n) mod 2 ^ n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite Z.mod_mod; try lia.
Qed.

Lemma signed_Lastnbits_mod_correct : forall x n, n > 0 -> x mod 2 ^ n = (signed_last_nbits x n) mod 2 ^ n.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))).
  - rewrite Z.mod_mod; try lia.
  - rewrite Zminus_mod. 
    rewrite Z.mod_mod; try lia.
    rewrite Z_mod_same_full. 
    rewrite Z.sub_0_r. 
    rewrite Z.mod_mod; try lia.
Qed. 

Lemma unsigned_Lastnbits_range : forall x n, n > 0 -> 0 <= unsigned_last_nbits x n < 2 ^ n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  pose proof Z.mod_pos_bound x (2 ^ n).
  lia.
Qed.

Lemma signed_Lastnbits_range : forall x n, n > 0 -> - 2 ^ (n - 1) <= signed_last_nbits x n < 2 ^ (n - 1).
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))).
  - pose proof Z.mod_pos_bound x (2 ^ n).
    lia.
  - pose proof Z.mod_pos_bound x (2 ^ n).
    split ; try lia.
    assert (- 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1)).
    { 
      replace n with (n - 1 + 1) at 2 by lia.
      rewrite Z.pow_add_r ; lia.
    }
    lia.
Qed.

Lemma unsigned_last_nbits_eq : forall x n, 0 <= x < 2 ^ n -> unsigned_last_nbits x n = x.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite Z.mod_small; lia.
Qed.

Lemma signed_last_nbits_eq : forall x n, n > 0 -> - 2 ^ (n - 1) <= x < 2 ^ (n - 1) -> signed_last_nbits x n = x.
Proof.
  intros.
  unfold signed_last_nbits.
  assert (- 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1)).
  { 
    replace n with (n - 1 + 1) at 2 by lia.
    rewrite Z.pow_add_r ; lia.
  }
  destruct (zlt x 0); destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))).
  - rewrite Z.mod_small ; try lia.
    pose proof (Z.div_mod x (2 ^ n) (ltac:(lia))).
    pose proof (Z.mod_pos_bound x (2 ^ n) (ltac:(lia))).
    assert (x / 2 ^ n = -1 -> False).
    {
      intros. 
      rewrite H4 in H2.
      replace (2 ^ n * (-1)) with (- 2 ^ n) in H1 by lia.
      assert (x < - 2 ^ n + 2 ^ (n-1)) by lia.
      lia.
    }
    assert (x / 2 ^ n <= -2) by lia.
    exfalso.
    assert (2 ^ n * (x / 2 ^ n) <= 2 ^ n * (-2)).
    { 
      apply Z.mul_le_mono_nonneg_l ; lia.
    }
    lia.  
  - pose proof (Z.div_mod x (2 ^ n) (ltac:(lia))).
    pose proof (Z.mod_pos_bound x (2 ^ n) (ltac:(lia))).
    assert (x / 2 ^ n <= -1) by lia.
    assert (x / 2 ^ n < -1 -> False).
    { 
       intros. 
       assert (2 ^ n * (x / 2 ^ n) <= 2 ^ n * (-2)).
       {
          apply Z.mul_le_mono_nonneg_l ; lia.  
       }
       lia.
    }
    assert (x / 2 ^ n = -1) by lia.
    lia.
  - rewrite Z.mod_small ; lia.
  - exfalso.
    pose proof (Z.div_mod x (2 ^ n) (ltac:(lia))).
    assert (x / 2^n >= 0).
    {
      apply Z_div_ge0 ; lia.
    }
    lia. 
Qed.

Lemma Int_signed_eq : forall x, Int.min_signed <= x <= Int.max_signed -> x = signed_last_nbits x 32.
Proof.
  intros.
  rewrite signed_last_nbits_eq ; try lia.
  replace (Int.min_signed) with (- 2 ^ 31) in H by reflexivity.
  replace (Int.max_signed) with (2 ^ 31 - 1) in H by reflexivity.
  lia.
Qed.

Lemma UInt_unsigned_eq : forall x, 0 <= x <= Int.max_unsigned -> x = unsigned_last_nbits x 32.
Proof. 
  intros.
  rewrite unsigned_last_nbits_eq ; try lia.
  replace (Int.max_unsigned) with (2 ^ 32 - 1) in H by reflexivity.
  lia.
Qed.

Lemma Int64_signed_eq : forall x, Int64.min_signed <= x <= Int64.max_signed -> x = signed_last_nbits x 64.
Proof. 
  intros.
  rewrite signed_last_nbits_eq ; try lia.
  replace (Int64.min_signed) with (- 2 ^ 63) in H by reflexivity.
  replace (Int64.max_signed) with (2 ^ 63 - 1) in H by reflexivity.
  lia.
Qed. 

Lemma UInt64_unsigned_eq : forall x, 0 <= x <= Int64.max_unsigned -> x = unsigned_last_nbits x 64.
Proof.
  intros.
  rewrite unsigned_last_nbits_eq ; try lia.
  replace (Int64.max_unsigned) with (2 ^ 64 - 1) in H by reflexivity.
  lia.
Qed.

Lemma unsigned_unsigned_add_l : forall x y n, n > 0 ->
  unsigned_last_nbits (unsigned_last_nbits x n + y) n = 
  unsigned_last_nbits (x + y) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite Z.add_mod_idemp_l; try lia.
Qed.

Lemma unsigned_unsigned_add_r : forall x y n, n > 0 ->
  unsigned_last_nbits (x + unsigned_last_nbits y n) n = 
  unsigned_last_nbits (x + y) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite Z.add_mod_idemp_r; try lia.
Qed.

Lemma unsigned_unsigned_sub_l : forall x y n, n > 0 ->
  unsigned_last_nbits (unsigned_last_nbits x n - y) n = 
  unsigned_last_nbits (x - y) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite Zminus_mod_idemp_l ; lia.
Qed.

Lemma unsigned_unsigned_sub_r : forall x y n, n > 0 ->
  unsigned_last_nbits (x - unsigned_last_nbits y n) n = 
  unsigned_last_nbits (x - y) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite Zminus_mod_idemp_r; try lia.
Qed.


Lemma unsigned_unsigned_mul_l : forall x y n, n > 0 ->
  unsigned_last_nbits (unsigned_last_nbits x n * y) n = 
  unsigned_last_nbits (x * y) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite Z.mul_mod_idemp_l ; lia.
Qed.

Lemma unsigned_unsigned_mul_r : forall x y n, n > 0 ->
  unsigned_last_nbits (x * unsigned_last_nbits y n) n = 
  unsigned_last_nbits (x * y) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite Z.mul_mod_idemp_r; try lia.
Qed.

Lemma unsigned_unsigned_mul_l_add_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (unsigned_last_nbits x n * y + z) n = 
  unsigned_last_nbits (x * y + z) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Z.add_mod_idemp_l ; try lia.
  rewrite Z.mul_mod_idemp_l ; try lia.
  rewrite Z.add_mod_idemp_l ; try lia.
Qed.

Lemma unsigned_unsigned_mul_r_add_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (x * unsigned_last_nbits y n + z) n = 
  unsigned_last_nbits (x * y + z) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Z.add_mod_idemp_l ; try lia.
  rewrite Z.mul_mod_idemp_r ; try lia.
  rewrite Z.add_mod_idemp_l ; try lia.
Qed.

Lemma unsigned_unsigned_add_mul_l_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (x + unsigned_last_nbits y n * z) n = 
  unsigned_last_nbits (x + y * z) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Z.add_mod_idemp_r ; try lia.
  rewrite Z.mul_mod_idemp_l ; try lia.
  rewrite Z.add_mod_idemp_r ; try lia.
Qed.

Lemma unsigned_unsigned_add_mul_r_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (x + y * unsigned_last_nbits z n) n = 
  unsigned_last_nbits (x + y * z) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Z.add_mod_idemp_r ; try lia.
  rewrite Z.mul_mod_idemp_r ; try lia.
  rewrite Z.add_mod_idemp_r ; try lia.
Qed.

Lemma unsigned_unsigned_sub_mul_l_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (x - unsigned_last_nbits y n * z) n = 
  unsigned_last_nbits (x - y * z) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Zminus_mod_idemp_r ; try lia.
  rewrite Z.mul_mod_idemp_l ; try lia.
  rewrite Zminus_mod_idemp_r ; try lia.
Qed.

Lemma unsigned_unsigned_sub_mul_r_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (x - y * unsigned_last_nbits z n) n = 
  unsigned_last_nbits (x - y * z) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Zminus_mod_idemp_r ; try lia.
  rewrite Z.mul_mod_idemp_r ; try lia.
  rewrite Zminus_mod_idemp_r ; try lia.
Qed.

Lemma unsigned_unsigned_mul_l_sub_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (unsigned_last_nbits x n * y - z) n = 
  unsigned_last_nbits (x * y - z) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Zminus_mod_idemp_l ; try lia.
  rewrite Z.mul_mod_idemp_l ; try lia.
  rewrite Zminus_mod_idemp_l ; try lia.
Qed.

Lemma unsigned_unsigned_mul_r_sub_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (x * unsigned_last_nbits y n - z) n = 
  unsigned_last_nbits (x * y - z) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Zminus_mod_idemp_l ; try lia.
  rewrite Z.mul_mod_idemp_r ; try lia.
  rewrite Zminus_mod_idemp_l ; try lia.
Qed.

Lemma unsigned_unsigned_mul_l_mul_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (unsigned_last_nbits x n * y * z) n = 
  unsigned_last_nbits (x * y * z) n.
Proof.
  intros.
  rewrite <- Z.mul_assoc.
  rewrite unsigned_unsigned_mul_l ; try lia.
  rewrite Z.mul_assoc. lia.
Qed.

Lemma unsigned_unsigned_mul_r_mul_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (x * unsigned_last_nbits y n * z) n = 
  unsigned_last_nbits (x * (y * z)) n.
Proof.
  intros.
  rewrite Z.mul_comm. rewrite Z.mul_assoc.
  rewrite unsigned_unsigned_mul_r ; try lia.
  rewrite <- Z.mul_assoc. rewrite Z.mul_comm.
  rewrite <- Z.mul_assoc. lia.
Qed.

Lemma unsigned_unsigned_add_l_sub_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (unsigned_last_nbits x n + y - z) n = 
  unsigned_last_nbits (x + y - z) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Zminus_mod_idemp_l ; try lia.
  rewrite Z.add_mod_idemp_l ; try lia.
  rewrite Zminus_mod_idemp_l ; try lia.
Qed.

Lemma unsigned_unsigned_add_r_sub_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (x + unsigned_last_nbits y n - z) n = 
  unsigned_last_nbits (x + (y - z)) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Zminus_mod_idemp_l ; try lia.
  rewrite Z.add_mod_idemp_r ; try lia.
  rewrite Zminus_mod_idemp_l ; try lia.
  rewrite Z.add_sub_assoc. lia.
Qed.

Lemma unsigned_unsigned_add_l_add_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (unsigned_last_nbits x n + y + z) n = 
  unsigned_last_nbits (x + y + z) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Z.add_mod_idemp_l ; try lia.
  rewrite (Z.add_mod_idemp_l x y) ; try lia.
  rewrite Z.add_mod_idemp_l ; try lia.
Qed.

Lemma unsigned_unsigned_add_r_add_other : forall x y z n, n > 0 ->
  unsigned_last_nbits (x + unsigned_last_nbits y n + z) n = 
  unsigned_last_nbits (x + (y + z)) n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Z.add_mod_idemp_l ; try lia.
  rewrite Z.add_mod_idemp_r ; try lia.
  rewrite Z.add_mod_idemp_l ; try lia.
  rewrite Z.add_assoc. lia.
Qed.

Lemma unsigned_revolutive : forall x n, n > 0 ->
  unsigned_last_nbits (unsigned_last_nbits x n) n = 
  unsigned_last_nbits x n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite Z.mod_mod; try lia.
Qed.

Lemma Pow2Mod_less : forall x n m, n >= 0 -> m >= 0 -> n <= m ->
  x mod 2 ^ n = (x mod 2 ^ m) mod 2 ^ n.
Proof.
  intros.
  repeat rewrite <- Z.land_ones ; try lia.
  rewrite <- Z.land_assoc. symmetry.
  rewrite Z.land_ones ; try lia.
  rewrite Z.ones_mod_pow2 ; try lia.
Qed.

Lemma Pow2Mod_greater : forall x n m, n >= 0 -> m >= 0 -> n >= m ->
  x mod 2 ^ m = (x mod 2 ^ m) mod 2 ^ n.
Proof.
  intros.
  repeat rewrite <- Z.land_ones ; try lia.
  rewrite <- Z.land_assoc. symmetry.
  rewrite (Z.land_comm (Z.ones m)).
  rewrite Z.land_ones ; try lia.
  rewrite Z.ones_mod_pow2 ; try lia.
Qed.

Lemma unsigned_revolutive_less : forall x n m, n > 0 -> m > 0 -> n <= m ->
  unsigned_last_nbits (unsigned_last_nbits x m) n = 
  unsigned_last_nbits x n.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <-  Pow2Mod_less ; try lia.
Qed.

Lemma unsigned_revolutive_greater : forall x n m, n > 0 -> m > 0 -> n >= m ->
  unsigned_last_nbits (unsigned_last_nbits x m) n = 
  unsigned_last_nbits x m.
Proof.
  intros.
  unfold unsigned_last_nbits.
  rewrite <- Pow2Mod_greater ; try lia.
Qed.

Lemma signed_revolutive : forall x n, n > 0 ->
  signed_last_nbits (signed_last_nbits x n) n = 
  signed_last_nbits x n.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))) eqn: lt.
  - rewrite Z.mod_mod ; try lia. 
    rewrite lt. reflexivity.
  - rewrite <- Zminus_mod_idemp_r.
    rewrite Z_mod_same ; try lia. 
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite lt. reflexivity.
Qed.

Lemma Pow2Mod_zero : forall n m, n >= 0 -> m >= 0 -> n <= m ->
  (2 ^ m) mod (2 ^ n) = 0.
Proof.
  intros.
  rewrite Zdivide_mod ; try lia.
  hnf. exists (2 ^ (m - n)).
  rewrite <- Z.pow_add_r ; try lia.
  replace (m - n + n) with m by lia.
  reflexivity.
Qed.

Lemma Pow2Mod_self : forall n m, n >= 0 -> m >= 0 -> n > m ->
  (2 ^ m) mod (2 ^ n) = 2 ^ m.
Proof.
  intros.
  rewrite Zmod_small ; try lia.
  split ; try lia. 
  apply Z.pow_lt_mono_r ; try lia.
Qed.

Lemma signed_revolutive_less : forall x n m, n > 0 -> m > 0 -> n <= m ->
  signed_last_nbits (signed_last_nbits x m) n = 
  signed_last_nbits x n.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ m) (2 ^ (m - 1))) eqn: lt.
  - rewrite <- Pow2Mod_less ; try lia.
  - rewrite Zminus_mod. 
    rewrite <- Pow2Mod_less ; try lia. 
    rewrite Pow2Mod_zero ; try lia. 
    rewrite Z.sub_0_r. rewrite Z.mod_mod ; try lia.
Qed.

Lemma signed_revolutive_greater : forall x n m, n > 0 -> m > 0 -> n > m ->
  signed_last_nbits (signed_last_nbits x m) n = 
  signed_last_nbits x m.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ m) (2 ^ (m - 1))) eqn: lt.
  - rewrite <- Pow2Mod_greater ; try lia.
    assert (2 ^ (m - 1) < (2 ^ (n - 1))).
    {
      apply Z.pow_lt_mono_r; try lia.
    }
    destruct (zlt (x mod 2 ^ m) (2 ^ (n - 1))) ; try lia.
  - replace (x mod 2 ^ m - 2 ^ m) with (- (2 ^ m - (x mod 2 ^ m))) by lia.
    assert (2 ^ m - x mod 2 ^ m < 2 ^ (n - 1)).
    {
      assert (2 ^ m <= 2 ^ (n - 1)). {
        apply Z.pow_le_mono_r; try lia.
      }
      pose proof (Z_mod_lt x (2 ^ m)).
      lia.
    }
    assert (forall n , n >= 0 -> 2 ^ n > 0).
    {
      intros. pose proof Z.pow_pos; lia. 
    }
    assert (0 <= 2 ^ m - x mod 2 ^ m < 2 ^ n).
    {
      pose proof (Z_mod_lt x (2 ^ m)).
      split; try lia.
      assert (2 ^ m < 2 ^ n). {
        apply Z.pow_lt_mono_r; try lia.
      }
      lia. 
    }
    rewrite Z.mod_opp_l_nz ; try lia ; rewrite Z.mod_small ; try lia.
    * destruct (zlt (2 ^ n - (2 ^ m - x mod 2 ^ m)) (2 ^ (n - 1))) ; try lia.
      replace (2 ^ n) with (2 ^ (n - 1 + 1)) in l at 1.
      rewrite Z.pow_add_r in l ; try lia. 
      replace (n - 1 + 1) with n by lia. lia.
    * pose proof Z.mod_pos_bound x (2 ^ m).
      lia.
Qed.

Lemma signed_unsigned_revolutive : forall x n, n > 0 ->
  signed_last_nbits (unsigned_last_nbits x n) n = 
  signed_last_nbits x n.
Proof.
  intros.
  unfold signed_last_nbits, unsigned_last_nbits.
  rewrite Z.mod_mod; try lia.
Qed.

Lemma signed_unsigned_revolutive_less : forall x n m, n > 0 -> m > 0 -> n <= m ->
  signed_last_nbits (unsigned_last_nbits x m) n = 
  signed_last_nbits x n.
Proof.
  intros.
  unfold signed_last_nbits, unsigned_last_nbits.
  rewrite <- Pow2Mod_less ; try lia.
Qed.

Lemma signed_unsigned_revolutive_greater : forall x n m, n > 0 -> m > 0 -> n > m ->
  signed_last_nbits (unsigned_last_nbits x m) n = 
  unsigned_last_nbits x m.
Proof.
  intros.
  unfold signed_last_nbits, unsigned_last_nbits.
  rewrite <- Pow2Mod_greater ; try lia.
  assert (2 ^ m <= (2 ^ (n - 1))).
  {
    apply Z.pow_le_mono_r; try lia.
  }
  pose proof (Z.mod_pos_bound x (2 ^ m)). 
  destruct (zlt (x mod 2 ^ m) (2 ^ (n - 1))) ; try lia.
Qed.

Lemma unsigned_signed_revolutive : forall x n, n > 0 ->
  unsigned_last_nbits (signed_last_nbits x n) n = 
  unsigned_last_nbits x n.
Proof.
  intros.
  unfold signed_last_nbits, unsigned_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))) eqn: lt.
  - rewrite Z.mod_mod; try lia.
  - rewrite <- Zminus_mod_idemp_r.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
Qed.

Lemma unsigned_signed_revolutive_less : forall x n m, n > 0 -> m > 0 -> n <= m ->
  unsigned_last_nbits (signed_last_nbits x m) n = 
  unsigned_last_nbits x n.
Proof.
  intros.
  unfold signed_last_nbits, unsigned_last_nbits.
  destruct (zlt (x mod 2 ^ m) (2 ^ (m - 1))) eqn: lt.
  - rewrite <- Pow2Mod_less ; try lia.
  - rewrite Zminus_mod. 
    rewrite <- Pow2Mod_less ; try lia. 
    rewrite Pow2Mod_zero ; try lia. 
    rewrite Z.sub_0_r. rewrite Z.mod_mod ; try lia.
Qed.

Lemma unsigned_signed_revolutive_greater_pos : forall x n m, n > 0 -> m > 0 -> n > m -> signed_last_nbits x m >= 0 ->
  unsigned_last_nbits (signed_last_nbits x m) n = 
  unsigned_last_nbits x m.
Proof.
  intros.
  unfold signed_last_nbits, unsigned_last_nbits in *.
  destruct (zlt (x mod 2 ^ m) (2 ^ (m - 1))) eqn: lt.
  - rewrite <- Pow2Mod_greater ; try lia.
  - pose proof Z.mod_pos_bound x (2 ^ m).
    lia.
Qed.

Lemma unsigned_signed_revolutive_greater_neg : forall x n m, n > 0 -> m > 0 -> n > m -> signed_last_nbits x m < 0 ->
  unsigned_last_nbits (signed_last_nbits x m) n = 
  2 ^ n - 2 ^ m + unsigned_last_nbits x m.
Proof.
  intros.
  unfold signed_last_nbits, unsigned_last_nbits in *.
  destruct (zlt (x mod 2 ^ m) (2 ^ (m - 1))) eqn: lt.
  - pose proof Z.mod_pos_bound x (2 ^ m). lia.
  - replace (x mod 2 ^ m - 2 ^ m) with (- (2 ^ m - (x mod 2 ^ m))) by lia.
    assert (2 ^ m - x mod 2 ^ m < 2 ^ (n - 1)).
    {
      assert (2 ^ m <= 2 ^ (n - 1)). {
        apply Z.pow_le_mono_r; try lia.
      }
      pose proof (Z_mod_lt x (2 ^ m)).
      lia.
    }
    assert (forall n , n >= 0 -> 2 ^ n > 0).
    {
      intros. pose proof Z.pow_pos; lia. 
    }
    assert (0 <= 2 ^ m - x mod 2 ^ m < 2 ^ n).
    {
      pose proof (Z_mod_lt x (2 ^ m)).
      split; try lia.
      assert (2 ^ m < 2 ^ n). {
        apply Z.pow_lt_mono_r; try lia.
      }
      lia. 
    }
    rewrite Z.mod_opp_l_nz ; try lia ; rewrite Z.mod_small ; try lia.
Qed.

Lemma signed_unsigned_sub_l : forall x y n, n > 0 ->
  signed_last_nbits (unsigned_last_nbits x n - y) n = 
  signed_last_nbits (x - y) n.
Proof.
  intros.
  unfold signed_last_nbits , unsigned_last_nbits.
  rewrite Zminus_mod_idemp_l ; try lia.
Qed.

Lemma signed_unsigned_sub_r : forall x y n, n > 0 ->
  signed_last_nbits (x - unsigned_last_nbits y n) n = 
  signed_last_nbits (x - y) n.
Proof.
  intros.
  unfold signed_last_nbits , unsigned_last_nbits.
  rewrite Zminus_mod_idemp_r ; try lia.
Qed.

Lemma signed_unsigned_add_l : forall x y n, n > 0 ->
  signed_last_nbits (unsigned_last_nbits x n + y) n = 
  signed_last_nbits (x + y) n.
Proof.
  intros.
  unfold signed_last_nbits , unsigned_last_nbits.
  rewrite Z.add_mod_idemp_l ; try lia.
Qed.

Lemma signed_unsigned_add_r : forall x y n, n > 0 ->
  signed_last_nbits (x + unsigned_last_nbits y n) n = 
  signed_last_nbits (x + y) n.
Proof.
  intros.
  unfold signed_last_nbits , unsigned_last_nbits.
  rewrite Z.add_mod_idemp_r ; try lia.
Qed.

Lemma signed_unsigned_mul_l : forall x y n, n > 0 ->
  signed_last_nbits (unsigned_last_nbits x n * y) n = 
  signed_last_nbits (x * y) n.
Proof.
  intros.
  unfold signed_last_nbits , unsigned_last_nbits.
  rewrite Z.mul_mod_idemp_l ; try lia.
Qed.

Lemma signed_unsigned_mul_r : forall x y n, n > 0 ->
  signed_last_nbits (x * unsigned_last_nbits y n) n = 
  signed_last_nbits (x * y) n.
Proof.
  intros.
  unfold signed_last_nbits , unsigned_last_nbits.
  rewrite Z.mul_mod_idemp_r ; try lia.
Qed.

Lemma signed_signed_add_r : forall x y n, n > 0 ->
  signed_last_nbits (x + signed_last_nbits y n) n = 
  signed_last_nbits (x + y) n.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (y mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Z.add_mod_idemp_r ; try lia.
  - rewrite <- Z.add_mod_idemp_r ; try lia.
    rewrite <- Zminus_mod_idemp_r ; try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Z.add_mod_idemp_r ; try lia.
Qed.

Lemma signed_signed_add_l : forall x y n, n > 0 ->
  signed_last_nbits (signed_last_nbits x n + y) n = 
  signed_last_nbits (x + y) n.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Z.add_mod_idemp_l ; try lia.
  - rewrite <- Z.add_mod_idemp_l ; try lia.
    rewrite <- Zminus_mod_idemp_r ; try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Z.add_mod_idemp_l ; try lia.
Qed.

Lemma signed_signed_sub_r : forall x y n, n > 0 ->
  signed_last_nbits (x - signed_last_nbits y n) n = 
  signed_last_nbits (x - y) n.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (y mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Zminus_mod_idemp_r ; try lia.
  - rewrite <- Zminus_mod_idemp_r ; try lia.
    rewrite <- (Zminus_mod_idemp_r (y mod 2 ^ n)) ; try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Zminus_mod_idemp_r ; try lia.
Qed.

Lemma signed_signed_sub_l : forall x y n, n > 0 ->
  signed_last_nbits (signed_last_nbits x n - y) n = 
  signed_last_nbits (x - y) n.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Zminus_mod_idemp_l ; try lia.
  - rewrite <- Zminus_mod_idemp_l ; try lia.
    rewrite <- (Zminus_mod_idemp_r (x mod 2 ^ n)) ; try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Zminus_mod_idemp_l ; try lia.
Qed.

Lemma signed_signed_mul_l : forall x y n, n > 0 ->
  signed_last_nbits (signed_last_nbits x n * y) n = 
  signed_last_nbits (x * y) n.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Z.mul_mod_idemp_l ; try lia.
  - rewrite <- Z.mul_mod_idemp_l ; try lia.
    rewrite <- (Zminus_mod_idemp_r (x mod 2 ^ n)) ; try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Z.mul_mod_idemp_l ; try lia.
Qed.

Lemma signed_signed_mul_r : forall x y n, n > 0 ->
  signed_last_nbits (x * signed_last_nbits y n) n = 
  signed_last_nbits (x * y) n.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (y mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Z.mul_mod_idemp_r ; try lia.
  - rewrite <- Z.mul_mod_idemp_r ; try lia.
    rewrite <- (Zminus_mod_idemp_r (y mod 2 ^ n)) ; try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Z.mul_mod_idemp_r ; try lia.
Qed.

Lemma unsigned_signed_add_l : forall x y n, n > 0 ->
  unsigned_last_nbits (signed_last_nbits x n + y) n = 
  unsigned_last_nbits (x + y) n.
Proof.
  intros.
  unfold unsigned_last_nbits, signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Z.add_mod_idemp_l ; try lia.
  - rewrite <- Z.add_mod_idemp_l ; try lia.
    rewrite <- Zminus_mod_idemp_r ; try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Z.add_mod_idemp_l ; try lia.
Qed.

Lemma unsigned_signed_add_r : forall x y n, n > 0 ->
  unsigned_last_nbits (x + signed_last_nbits y n) n = 
  unsigned_last_nbits (x + y) n.
Proof.
  intros.
  unfold unsigned_last_nbits, signed_last_nbits.
  destruct (zlt (y mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Z.add_mod_idemp_r ; try lia.
  - rewrite <- Z.add_mod_idemp_r ; try lia.
    rewrite <- Zminus_mod_idemp_r ; try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Z.add_mod_idemp_r ; try lia.
Qed.

Lemma unsigned_signed_sub_l : forall x y n, n > 0 ->
  unsigned_last_nbits (signed_last_nbits x n - y) n = 
  unsigned_last_nbits (x - y) n.
Proof.
  intros.
  unfold unsigned_last_nbits, signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Zminus_mod_idemp_l ; try lia.
  - rewrite <- Zminus_mod_idemp_l ; try lia.
    rewrite <- (Zminus_mod_idemp_r (x mod 2^n)); try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Zminus_mod_idemp_l ; try lia.
Qed.

Lemma unsigned_signed_sub_r : forall x y n, n > 0 ->
  unsigned_last_nbits (x - signed_last_nbits y n) n = 
  unsigned_last_nbits (x - y) n.
Proof.
  intros.
  unfold unsigned_last_nbits, signed_last_nbits.
  destruct (zlt (y mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Zminus_mod_idemp_r ; try lia.
  - rewrite <- Zminus_mod_idemp_r ; try lia.
    rewrite <- (Zminus_mod_idemp_r (y mod 2^n)); try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Zminus_mod_idemp_r ; try lia.
Qed.

Lemma unsigned_signed_mul_l : forall x y n, n > 0 ->
  unsigned_last_nbits (signed_last_nbits x n * y) n = 
  unsigned_last_nbits (x * y) n.
Proof.
  intros.
  unfold unsigned_last_nbits, signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Z.mul_mod_idemp_l ; try lia.
  - rewrite <- Z.mul_mod_idemp_l ; try lia.
    rewrite <- (Zminus_mod_idemp_r (x mod 2^n)); try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Z.mul_mod_idemp_l ; try lia.
Qed.

Lemma unsigned_signed_mul_r : forall x y n, n > 0 ->
  unsigned_last_nbits (x * signed_last_nbits y n) n = 
  unsigned_last_nbits (x * y) n.
Proof.
  intros.
  unfold unsigned_last_nbits, signed_last_nbits.
  destruct (zlt (y mod 2 ^ n) (2 ^ (n - 1))) eqn: lt1.
  - rewrite Z.mul_mod_idemp_r ; try lia.
  - rewrite <- Z.mul_mod_idemp_r ; try lia.
    rewrite <- (Zminus_mod_idemp_r (y mod 2^n)); try lia.
    rewrite Z_mod_same ; try lia.
    rewrite Zminus_0_r. rewrite Z.mod_mod ; try lia.
    rewrite Z.mul_mod_idemp_r ; try lia.
Qed.


Ltac unsigned_unsigned_simpl :=
  repeat progress
  match goal with 
    | |- context [unsigned_last_nbits (unsigned_last_nbits ?x ?n + ?y) ?n] => rewrite (unsigned_unsigned_add_l x y n) ; try lia
    | |- context [unsigned_last_nbits (?x + unsigned_last_nbits ?y ?n) ?n] => rewrite (unsigned_unsigned_add_r x y n) ; try lia
    | |- context [unsigned_last_nbits (unsigned_last_nbits ?x ?n - ?y) ?n] => rewrite (unsigned_unsigned_sub_l x y n) ; try lia
    | |- context [unsigned_last_nbits (?x - unsigned_last_nbits ?y ?n) ?n] => rewrite (unsigned_unsigned_sub_r x y n) ; try lia
    | |- context [unsigned_last_nbits (unsigned_last_nbits ?x ?n * ?y) ?n] => rewrite (unsigned_unsigned_mul_l x y n) ; try lia
    | |- context [unsigned_last_nbits (?x * unsigned_last_nbits ?y ?n) ?n] => rewrite (unsigned_unsigned_mul_r x y n) ; try lia
    | |- context [unsigned_last_nbits (unsigned_last_nbits ?x ?n) ?n] => rewrite (unsigned_revolutive x n) ; try lia
    | |- context [unsigned_last_nbits (unsigned_last_nbits ?x ?n * ?y + ?z) ?n] => rewrite (unsigned_unsigned_mul_l_add_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (?x * unsigned_last_nbits ?y ?n + ?z) ?n] => rewrite (unsigned_unsigned_mul_r_add_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (unsigned_last_nbits ?x ?n * ?y - ?z) ?n] => rewrite (unsigned_unsigned_mul_l_sub_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (?x * unsigned_last_nbits ?y ?n - ?z) ?n] => rewrite (unsigned_unsigned_mul_r_sub_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (unsigned_last_nbits ?x ?n + ?y - ?z) ?n] => rewrite (unsigned_unsigned_add_l_sub_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (?x + unsigned_last_nbits ?y ?n - ?z) ?n] => rewrite (unsigned_unsigned_add_r_sub_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (unsigned_last_nbits ?x ?n * ?y * ?z) ?n] => rewrite (unsigned_unsigned_mul_l_mul_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (?x * unsigned_last_nbits ?y ?n * ?z) ?n] => rewrite (unsigned_unsigned_mul_r_mul_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (unsigned_last_nbits ?x ?n + ?y + ?z) ?n] => rewrite (unsigned_unsigned_add_l_add_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (?x + unsigned_last_nbits ?y ?n + ?z) ?n] => rewrite (unsigned_unsigned_add_r_add_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (?x + unsigned_last_nbits ?y ?n * ?z) ?n] => rewrite (unsigned_unsigned_add_mul_l_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (?x + ?y * unsigned_last_nbits ?z ?n) ?n] => rewrite (unsigned_unsigned_add_mul_r_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (?x - unsigned_last_nbits ?y ?n * ?z) ?n] => rewrite (unsigned_unsigned_sub_mul_l_other x y z n) ; try lia
    | |- context [unsigned_last_nbits (?x - ?y * unsigned_last_nbits ?z ?n) ?n] => rewrite (unsigned_unsigned_sub_mul_r_other x y z n) ; try lia
    | |- unsigned_last_nbits ?x ?n = unsigned_last_nbits ?y ?n => try (f_equal ; lia)
  end.

Ltac signed_signed_simpl :=
  repeat progress
  match goal with 
    | |- context [signed_last_nbits (signed_last_nbits ?x ?n + ?y) ?n] => rewrite (signed_signed_add_l x y n) ; try lia
    | |- context [signed_last_nbits (?x + signed_last_nbits ?y ?n) ?n] => rewrite (signed_signed_add_r x y n) ; try lia
    | |- context [signed_last_nbits (signed_last_nbits ?x ?n - ?y) ?n] => rewrite (signed_signed_sub_l x y n) ; try lia
    | |- context [signed_last_nbits (?x - signed_last_nbits ?y ?n) ?n] => rewrite (signed_signed_sub_r x y n) ; try lia
    | |- context [signed_last_nbits (signed_last_nbits ?x ?n * ?y) ?n] => rewrite (signed_signed_mul_l x y n) ; try lia
    | |- context [signed_last_nbits (?x * signed_last_nbits ?y ?n) ?n] => rewrite (signed_signed_mul_r x y n) ; try lia
    | |- context [signed_last_nbits (signed_last_nbits ?x ?n) ?n] => rewrite (signed_revolutive x n) ; try lia
    | |- signed_last_nbits ?x ?n = signed_last_nbits ?y ?n => try (f_equal ; lia)
  end.

Ltac unsigned_signed_simpl :=
  repeat progress
  match goal with 
    | |- context [unsigned_last_nbits (signed_last_nbits ?x ?n + ?y) ?n] => rewrite (unsigned_signed_add_l x y n) ; try lia
    | |- context [unsigned_last_nbits (?x + signed_last_nbits ?y ?n) ?n] => rewrite (unsigned_signed_add_r x y n) ; try lia
    | |- context [unsigned_last_nbits (signed_last_nbits ?x ?n - ?y) ?n] => rewrite (unsigned_signed_sub_l x y n) ; try lia
    | |- context [unsigned_last_nbits (?x - signed_last_nbits ?y ?n) ?n] => rewrite (unsigned_signed_sub_r x y n) ; try lia
    | |- context [unsigned_last_nbits (signed_last_nbits ?x ?n * ?y) ?n] => rewrite (unsigned_signed_mul_l x y n) ; try lia
    | |- context [unsigned_last_nbits (?x * signed_last_nbits ?y ?n) ?n] => rewrite (unsigned_signed_mul_r x y n) ; try lia
    | |- context [unsigned_last_nbits (signed_last_nbits ?x ?n) ?n] => rewrite (unsigned_signed_revolutive x n) ; try lia
  end.

Ltac signed_unsigned_simpl :=
  repeat progress
  match goal with 
    | |- context [signed_last_nbits (unsigned_last_nbits ?x ?n + ?y) ?n] => rewrite (signed_unsigned_add_l x y n) ; try lia
    | |- context [signed_last_nbits (?x + unsigned_last_nbits ?y ?n) ?n] => rewrite (signed_unsigned_add_r x y n) ; try lia
    | |- context [signed_last_nbits (unsigned_last_nbits ?x ?n - ?y) ?n] => rewrite (signed_unsigned_sub_l x y n) ; try lia
    | |- context [signed_last_nbits (?x - unsigned_last_nbits ?y ?n) ?n] => rewrite (signed_unsigned_sub_r x y n) ; try lia
    | |- context [signed_last_nbits (unsigned_last_nbits ?x ?n * ?y) ?n] => rewrite (signed_unsigned_mul_l x y n) ; try lia
    | |- context [signed_last_nbits (?x * unsigned_last_nbits ?y ?n) ?n] => rewrite (signed_unsigned_mul_r x y n) ; try lia
    | |- context [signed_last_nbits (unsigned_last_nbits ?x ?n) ?n] => rewrite (signed_unsigned_revolutive x n) ; try lia
  end.

Ltac lastnbits_simpl := 
  repeat progress
  match goal with
    | |- context [unsigned_last_nbits ?x ?n] => 
      match x with 
        | context [unsigned_last_nbits ?y n] => unsigned_unsigned_simpl
        | context [signed_last_nbits ?y n] => unsigned_signed_simpl
      end 
    | |- context [signed_last_nbits ?x ?n] =>
      match x with 
        | context [unsigned_last_nbits ?y n] => signed_unsigned_simpl
        | context [signed_last_nbits ?y n] => signed_signed_simpl
      end
  end.


Ltac lastnbits_eq_step x :=
  match x with 
    | unsigned_last_nbits ?y ?n => rewrite (unsigned_last_nbits_eq y n) ; try lia
    | signed_last_nbits ?y ?n => rewrite (signed_last_nbits_eq y n) ; try lia
  end.

Ltac lastnbits_eq :=
  repeat progress
  match goal with
    | |- context [unsigned_last_nbits ?x ?n] => lastnbits_eq_step (unsigned_last_nbits x n)
    | |- context [signed_last_nbits ?x ?n] => lastnbits_eq_step (signed_last_nbits x n)
  end.

Lemma Ztestbits_unsigned_eq : forall x n m, m < n -> 
  Z.testbit (unsigned_last_nbits x n) m = Z.testbit x m.
Proof.
  intros.
  unfold unsigned_last_nbits.
  apply Z.mod_pow2_bits_low. auto.
Qed.

Lemma Ztestbits_unsigned_high : forall x n m, 0 <= n <= m -> 
  Z.testbit (unsigned_last_nbits x n) m = false.
Proof.
  intros.
  unfold unsigned_last_nbits.
  apply Z.mod_pow2_bits_high. auto.
Qed.

Lemma Ztestbits_signed_eq : forall x n m, 0 <= m < n -> 
  Z.testbit (signed_last_nbits x n) m = Z.testbit x m.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))).
  - apply Z.mod_pow2_bits_low. lia.
  - rewrite <- Z.add_opp_r.
    rewrite Zbits.Z_add_is_or ; try lia. 
    + rewrite Z.mod_pow2_bits_low ; try lia.
      replace (- 2 ^ n) with (- two_p n).
      2 : { rewrite two_p_equiv. reflexivity. }
      rewrite Zbits.Ztestbit_neg_two_p ; try lia. 
      destruct (zlt m n) ; try lia.
      rewrite orb_false_r. reflexivity.
    + intros. 
      rewrite Z.mod_pow2_bits_low ; try lia.
      replace (- 2 ^ n) with (- two_p n).
      2 : { rewrite two_p_equiv. reflexivity. }
      rewrite Zbits.Ztestbit_neg_two_p ; try lia.
      destruct (zlt j n) ; try lia.
Qed.

Lemma Ztestbits_signed_high_lt : forall x n m, 0 <= n <= m -> x mod 2 ^ n < 2 ^ (n - 1) ->
  Z.testbit (signed_last_nbits x n) m = false.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))) ; try lia.
  apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma Ztestbits_signed_high_ge : forall x n m, 0 <= n <= m -> x mod 2 ^ n >= 2 ^ (n - 1) ->
  Z.testbit (signed_last_nbits x n) m = true.
Proof.
  intros.
  unfold signed_last_nbits.
  destruct (zlt (x mod 2 ^ n) (2 ^ (n - 1))) ; try lia.
  rewrite <- Z.add_opp_r.
  rewrite Zbits.Z_add_is_or ; try lia.
  - rewrite Z.mod_pow2_bits_high ; try lia.
    replace (- 2 ^ n) with (- two_p n).
    2 : { rewrite two_p_equiv. reflexivity. }
    rewrite Zbits.Ztestbit_neg_two_p ; try lia.
    destruct (zlt m n) ; try lia.
  - intros.
    destruct (zle n j) ; try lia.
    + rewrite Z.mod_pow2_bits_high ; try lia.
    + replace (- 2 ^ n) with (- two_p n).
      2 : { rewrite two_p_equiv. reflexivity. }
      rewrite Zbits.Ztestbit_neg_two_p ; try lia.
      destruct (zlt j n) ; try lia.
Qed.

Lemma Ztestbits_signed_high : forall x n m, 0 <= n <= m ->
  Z.testbit (signed_last_nbits x n) m = (x mod 2 ^ n >=? 2 ^ (n - 1)).
Proof.
  intros.
  destruct (zle (2 ^ (n - 1)) (x mod 2 ^ n) ) eqn: ge.
  - rewrite Ztestbits_signed_high_ge ; try lia.
  - rewrite Ztestbits_signed_high_lt ; try lia.
Qed.
  
Theorem unsigned_last_nbits_land_distr : forall x y n, 0 <= n -> unsigned_last_nbits (Z.land x y) n = Z.land (unsigned_last_nbits x n) (unsigned_last_nbits y n).
Proof.
  intros.
  apply Z.bits_inj'.
  intros.
  rewrite Z.land_spec.
  destruct (n0 <? n) eqn: lt.
  - repeat rewrite Ztestbits_unsigned_eq ; try lia.
    rewrite Z.land_spec. reflexivity.
  - repeat rewrite Ztestbits_unsigned_high ; try lia.
Qed.

Theorem unsigned_last_nbits_lor_distr : forall x y n, 0 <= n -> unsigned_last_nbits (Z.lor x y) n = Z.lor (unsigned_last_nbits x n) (unsigned_last_nbits y n).
Proof.
  intros.
  apply Z.bits_inj'.
  intros.
  rewrite Z.lor_spec.
  destruct (n0 <? n) eqn: lt.
  - repeat rewrite Ztestbits_unsigned_eq ; try lia.
    rewrite Z.lor_spec. reflexivity.
  - repeat rewrite Ztestbits_unsigned_high ; try lia.
Qed.

Theorem unsigned_last_nbits_ldiff_distr : forall x y n, 0 <= n -> unsigned_last_nbits (Z.ldiff x y) n = Z.ldiff (unsigned_last_nbits x n) (unsigned_last_nbits y n).
Proof.
  intros.
  apply Z.bits_inj'.
  intros.
  rewrite Z.ldiff_spec.
  destruct (n0 <? n) eqn: lt.
  - repeat rewrite Ztestbits_unsigned_eq ; try lia.
    rewrite Z.ldiff_spec. reflexivity.
  - repeat rewrite Ztestbits_unsigned_high ; try lia.
Qed.

Theorem unsigned_last_nbits_lxor_distr : forall x y n, 0 <= n -> unsigned_last_nbits (Z.lxor x y) n = Z.lxor (unsigned_last_nbits x n) (unsigned_last_nbits y n).
Proof.
  intros.
  apply Z.bits_inj'.
  intros.
  rewrite Z.lxor_spec.
  destruct (n0 <? n) eqn: lt.
  - repeat rewrite Ztestbits_unsigned_eq ; try lia.
    rewrite Z.lxor_spec. reflexivity.
  - repeat rewrite Ztestbits_unsigned_high ; try lia.
    reflexivity.
Qed.

Theorem unsigned_last_nbits_land_missing_l : forall x y n, 0 <= n -> 
0 <= x < 2 ^ n -> 
unsigned_last_nbits (Z.land x y) n = Z.land x y.
Proof.
  intros.
  apply Z.bits_inj'.
  intros.
  rewrite Z.land_spec.
  destruct (n0 <? n) eqn: lt.
  - repeat rewrite Ztestbits_unsigned_eq ; try lia.
    rewrite Z.land_spec. reflexivity.
  - repeat rewrite Ztestbits_unsigned_high ; try lia.
    pose proof Zbits.Ztestbit_above (Z.to_nat n) x n0.
    replace (two_power_nat (Z.to_nat n)) with (2 ^ n) in H2 ; try lia.
    rewrite H2 ; try lia. 
    rewrite two_power_nat_equiv.
    replace (Z.of_nat (Z.to_nat n)) with n by lia. lia.
Qed.

Theorem unsigned_last_nbits_land_missing_r : forall x y n, 0 <= n -> 
0 <= y < 2 ^ n -> 
unsigned_last_nbits (Z.land x y) n = Z.land x y.
Proof.
  intros.
  rewrite Z.land_comm.
  rewrite unsigned_last_nbits_land_missing_l ; try lia.
Qed.

Theorem unsigned_last_nbits_land_clear_l : forall x y n, 0 <= n ->
Z.land (unsigned_last_nbits x n) (unsigned_last_nbits y n) = Z.land x (unsigned_last_nbits y n).
Proof.
  intros.
  apply Z.bits_inj'.
  intros.
  repeat rewrite Z.land_spec.
  destruct (n0 <? n) eqn: lt.
  - repeat rewrite Ztestbits_unsigned_eq ; try lia.
    reflexivity.
  - repeat rewrite Ztestbits_unsigned_high ; try lia.
Qed. 

Theorem unsigned_last_nbits_land_clear_r : forall x y n, 0 <= n ->
Z.land (unsigned_last_nbits x n) (unsigned_last_nbits y n) = Z.land (unsigned_last_nbits x n) y.
Proof.
  intros.
  apply Z.bits_inj'.
  intros.
  repeat rewrite Z.land_spec.
  destruct (n0 <? n) eqn: lt.
  - repeat rewrite Ztestbits_unsigned_eq ; try lia.
    reflexivity.
  - repeat rewrite Ztestbits_unsigned_high ; try lia.
Qed. 

Theorem unsigned_last_nbits_lor_distr_missing : forall x y n, 0 <= n -> 
0 <= x < 2 ^ n -> 0 <= y < 2 ^ n ->
unsigned_last_nbits (Z.lor x y) n = Z.lor x y.
Proof.
  intros.
  rewrite unsigned_last_nbits_lor_distr ; try lia.
  repeat rewrite unsigned_last_nbits_eq ; try lia.
Qed.

Theorem unsigned_last_nbits_ldiff_distr_missing_l : forall x y n, 0 <= n ->
  0 <= x < 2 ^ n -> 
unsigned_last_nbits (Z.ldiff x y) n = Z.ldiff x y.
Proof.
  intros.
  apply Z.bits_inj'.
  intros.
  rewrite Z.ldiff_spec.
  destruct (n0 <? n) eqn: lt.
  - repeat rewrite Ztestbits_unsigned_eq ; try lia.
    rewrite Z.ldiff_spec. reflexivity.
  - repeat rewrite Ztestbits_unsigned_high ; try lia.
    pose proof Zbits.Ztestbit_above (Z.to_nat n) x n0.
    rewrite two_power_nat_equiv in *.
    replace (Z.of_nat (Z.to_nat n)) with n in * by lia.
    rewrite H2 ; try lia.
Qed.

Theorem unsigned_last_nbits_lxor_distr_missing : forall x y n, 0 <= n ->
  0 <= x < 2 ^ n -> 0 <= y < 2 ^ n ->
unsigned_last_nbits (Z.lxor x y) n = Z.lxor x y.
Proof.
  intros.
  rewrite unsigned_last_nbits_lxor_distr ; try lia.
  repeat rewrite unsigned_last_nbits_eq ; try lia.
Qed.
