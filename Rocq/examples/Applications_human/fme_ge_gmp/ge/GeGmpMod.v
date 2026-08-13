Require Import Coq.ZArith.ZArith.
Require Export Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import GeGmpMatrix.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import GmpMul.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition vector : Type := Z -> Z.

Definition mod_congruent (p x y : Z) : Prop :=
  x mod p = y mod p.

Definition mod_norm_spec (p x r : Z) : Prop :=
  0 < p /\ 0 <= r < p /\ mod_congruent p r x.

Definition mod_inverse_spec (p a inv : Z) : Prop :=
  0 < p /\ 0 <= a < p /\ 0 <= inv < p /\ (a * inv) mod p = 1 mod p.

Definition mod_field (p : Z) : Prop :=
  2 <= p /\
  forall a, 0 < a < p -> exists inv, mod_inverse_spec p a inv.

Definition mod_inv_pow_loop
  (p a result base exp : Z) : Prop :=
  prime p /\
  0 < a < p /\
  0 <= result < p /\
  0 <= base < p /\
  0 <= exp /\
  (result * Z.pow base exp) mod p = Z.pow a (p - 2) mod p.

Lemma mod_congruent_pow : forall p x y e,
  p <> 0 -> 0 <= e -> x mod p = y mod p -> (x ^ e) mod p = (y ^ e) mod p.
Proof.
  intros p x y e Hp He Hxy.
  rewrite <- (Z2Nat.id e) by lia.
  remember (Z.to_nat e) as n eqn:Hn.
  clear He Hn e.
  induction n as [| n IH].
  - simpl. repeat rewrite Z.pow_0_r. reflexivity.
  - replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) by lia.
    repeat rewrite Z.pow_succ_r by lia.
    rewrite <- (Z.mul_mod_idemp_l x (x ^ Z.of_nat n) p) by exact Hp.
    rewrite <- (Z.mul_mod_idemp_l y (y ^ Z.of_nat n) p) by exact Hp.
    rewrite Hxy.
    rewrite <- (Z.mul_mod_idemp_r (y mod p) (x ^ Z.of_nat n) p) by exact Hp.
    rewrite <- (Z.mul_mod_idemp_r (y mod p) (y ^ Z.of_nat n) p) by exact Hp.
    rewrite IH.
    reflexivity.
Qed.

Lemma mod_inv_pow_loop_init : forall p a base,
  prime p -> 0 < a < p -> mod_norm_spec p a base -> mod_inv_pow_loop p a 1 base (p - 2).
Proof.
  intros p a base Hp Ha Hnorm.
  unfold mod_inv_pow_loop.
  destruct Hnorm as [_ [Hbase Hcong]].
  split; [exact Hp |].
  split; [exact Ha |].
  split.
  { pose proof (prime_ge_2 p Hp); lia. }
  split; [exact Hbase |].
  split.
  { pose proof (prime_ge_2 p Hp); lia. }
  unfold mod_congruent in Hcong.
  rewrite Z.mul_1_l.
  apply mod_congruent_pow; try lia.
Qed.

Lemma mod_mul_congruent : forall p x1 x2 y1 y2,
  p <> 0 ->
  x1 mod p = x2 mod p ->
  y1 mod p = y2 mod p ->
  (x1 * y1) mod p = (x2 * y2) mod p.
Proof.
  intros p x1 x2 y1 y2 Hp Hx Hy.
  rewrite <- (Z.mul_mod_idemp_l x1 y1 p) by exact Hp.
  rewrite <- (Z.mul_mod_idemp_r (x1 mod p) y1 p) by exact Hp.
  rewrite Hx, Hy.
  rewrite (Z.mul_mod_idemp_r (x2 mod p) y2 p) by exact Hp.
  rewrite (Z.mul_mod_idemp_l x2 y2 p) by exact Hp.
  reflexivity.
Qed.

Lemma pow_odd_decompose : forall b q,
  0 <= q -> b ^ (2 * q + 1) = b * (b * b) ^ q.
Proof.
  intros b q Hq.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  rewrite Z.pow_mul_r by lia.
  rewrite Z.pow_2_r.
  ring.
Qed.

Lemma pow_even_decompose : forall b q,
  0 <= q -> b ^ (2 * q) = (b * b) ^ q.
Proof.
  intros b q Hq.
  rewrite Z.pow_mul_r by lia.
  rewrite Z.pow_2_r.
  reflexivity.
Qed.

Lemma mod_inv_pow_loop_step_odd : forall p a result base exp result' base',
  mod_inv_pow_loop p a result base exp ->
  exp > 0 ->
  Z.rem exp 2 = 1 ->
  mod_norm_spec p (result * base) result' ->
  mod_norm_spec p (base * base) base' ->
  mod_inv_pow_loop p a result' base' (exp ÷ 2).
Proof.
  intros p a result base exp result' base' Hloop Hexp_pos Hodd Hnorm_res Hnorm_base.
  unfold mod_inv_pow_loop in *.
  destruct Hloop as [Hp [Ha [Hres [Hbase [Hexp_nonneg Hsem]]]]].
  destruct Hnorm_res as [_ [Hres' Hres_cong]].
  destruct Hnorm_base as [_ [Hbase' Hbase_cong]].
  unfold mod_congruent in Hres_cong, Hbase_cong.
  split; [exact Hp |].
  split; [exact Ha |].
  split; [exact Hres' |].
  split; [exact Hbase' |].
  split.
  { apply Z.quot_pos; lia. }
  set (q := exp ÷ 2).
  assert (Hq_nonneg : 0 <= q) by (subst q; apply Z.quot_pos; lia).
  assert (Hexp_eq : exp = 2 * q + 1).
  { subst q. pose proof (Z.quot_rem exp 2 ltac:(lia)). lia. }
  assert (Hpow_cong : base' ^ q mod p = (base * base) ^ q mod p).
  { apply mod_congruent_pow; try lia. }
  assert (Hmul_cong : (result' * base' ^ q) mod p = ((result * base) * (base * base) ^ q) mod p).
  { apply mod_mul_congruent; try lia. }
  rewrite Hmul_cong.
  replace ((result * base) * (base * base) ^ q) with (result * (base * (base * base) ^ q)) by ring.
  rewrite <- pow_odd_decompose by lia.
  rewrite <- Hexp_eq.
  exact Hsem.
Qed.

Lemma mod_inv_pow_loop_step_even : forall p a result base exp base',
  mod_inv_pow_loop p a result base exp ->
  exp > 0 ->
  Z.rem exp 2 = 0 ->
  mod_norm_spec p (base * base) base' ->
  mod_inv_pow_loop p a result base' (exp ÷ 2).
Proof.
  intros p a result base exp base' Hloop Hexp_pos Heven Hnorm_base.
  unfold mod_inv_pow_loop in *.
  destruct Hloop as [Hp [Ha [Hres [Hbase [Hexp_nonneg Hsem]]]]].
  destruct Hnorm_base as [_ [Hbase' Hbase_cong]].
  unfold mod_congruent in Hbase_cong.
  split; [exact Hp |].
  split; [exact Ha |].
  split; [exact Hres |].
  split; [exact Hbase' |].
  split.
  { apply Z.quot_pos; lia. }
  set (q := exp ÷ 2).
  assert (Hq_nonneg : 0 <= q) by (subst q; apply Z.quot_pos; lia).
  assert (Hexp_eq : exp = 2 * q).
  { subst q. pose proof (Z.quot_rem exp 2 ltac:(lia)). lia. }
  assert (Hpow_cong : base' ^ q mod p = (base * base) ^ q mod p).
  { apply mod_congruent_pow; try lia. }
  pose proof (mod_mul_congruent p result result (base' ^ q) ((base * base) ^ q)
                ltac:(lia) ltac:(reflexivity) Hpow_cong) as Hmul_cong.
  rewrite Hmul_cong.
  rewrite <- pow_even_decompose by lia.
  rewrite <- Hexp_eq.
  exact Hsem.
Qed.

Definition residues (p : Z) : list Z :=
  map Z.of_nat (seq 1 (Z.to_nat (p - 1))).

Fixpoint zprod (l : list Z) : Z :=
  match l with
  | nil => 1
  | x :: xs => x * zprod xs
  end.

Lemma NoDup_map_Zof_nat_seq : forall start len,
  NoDup (map Z.of_nat (seq start len)).
Proof.
  intros.
  apply NoDup_map_NoDup_ForallPairs.
  - unfold ForallPairs. intros a b _ _ Heq.
    apply Nat2Z.inj in Heq. exact Heq.
  - apply seq_NoDup.
Qed.

Lemma residues_nodup : forall p,
  NoDup (residues p).
Proof.
  intros p. unfold residues. apply NoDup_map_Zof_nat_seq.
Qed.

Lemma in_residues : forall p x,
  1 < p -> In x (residues p) <-> 1 <= x < p.
Proof.
  intros p x Hp.
  unfold residues.
  rewrite in_map_iff.
  split.
  - intros [n [Hx Hin]].
    subst x.
    apply in_seq in Hin.
    zify; lia.
  - intros Hx.
    exists (Z.to_nat x).
    split.
    + rewrite Z2Nat.id by lia. reflexivity.
    + apply in_seq. zify; lia.
Qed.

Lemma prime_mul_mod_cancel : forall p a x y,
  prime p -> 0 < a < p -> 1 <= x < p -> 1 <= y < p ->
  (a * x) mod p = (a * y) mod p -> x = y.
Proof.
  intros p a x y Hp Ha Hx Hy Heq.
  pose proof (prime_ge_2 p Hp) as Hp2.
  assert (Hdiv : (p | a * (x - y))).
  { apply Zmod_divide; [lia|].
    replace (a * (x - y)) with (a * x - a * y) by ring.
    rewrite Zminus_mod.
    rewrite Heq.
    rewrite Z.sub_diag.
    apply Z.mod_0_l; lia. }
  assert (Hrel : rel_prime p a).
  { apply rel_prime_sym.
    destruct Hp as [Hpgt Hall].
    apply Hall; lia. }
  pose proof (Gauss p a (x - y) Hdiv Hrel) as Hdivxy.
  destruct Hdivxy as [k Hk].
  assert (-p < x - y < p) by lia.
  subst.
  assert (-1 < k) by (apply (Zmult_lt_reg_r (-1) k p); lia).
  assert (k < 1) by (apply (Zmult_lt_reg_r k 1 p); lia).
  lia.
Qed.

Lemma prime_mul_residue_in_residues : forall p a x,
  prime p -> 0 < a < p -> In x (residues p) ->
  In ((a * x) mod p) (residues p).
Proof.
  intros p a x Hp Ha Hx.
  pose proof (prime_ge_2 p Hp) as Hp2.
  apply in_residues; [lia|].
  apply in_residues in Hx; [|lia].
  split.
  - assert (Hrel_pa : rel_prime p a).
    { apply rel_prime_sym.
      destruct Hp as [Hpgt Hall].
      apply Hall; lia. }
    assert (Hrel_px : rel_prime p x).
    { apply rel_prime_sym.
      destruct Hp as [Hpgt Hall].
      apply Hall; lia. }
    pose proof (rel_prime_mult p a x Hrel_pa Hrel_px) as Hrel_p_ax.
    pose proof (Zrel_prime_neq_mod_0 (a * x) p ltac:(lia)
                  (rel_prime_sym _ _ Hrel_p_ax)) as Hnz.
    pose proof (Z.mod_pos_bound (a * x) p ltac:(lia)) as Hbound.
    lia.
  - apply Z.mod_pos_bound; lia.
Qed.

Lemma prime_mul_residue_preimage : forall p a z,
  prime p -> 0 < a < p -> In z (residues p) ->
  exists x, (a * x) mod p = z /\ In x (residues p).
Proof.
  intros p a z Hp Ha Hz.
  pose proof (prime_ge_2 p Hp) as Hp2.
  assert (Hrel_ap : rel_prime a p).
  { destruct Hp as [Hpgt Hall]. apply Hall; lia. }
  pose proof (rel_prime_bezout a p Hrel_ap) as Hbez.
  destruct Hbez as [u v Huv].
  exists ((u * z) mod p).
  assert (Hzrange : 1 <= z < p).
  { apply in_residues in Hz; lia. }
  assert (Hmap : (a * ((u * z) mod p)) mod p = z).
  { rewrite (Z.mul_mod_idemp_r a (u * z) p) by lia.
    replace (a * (u * z)) with ((u * a) * z) by ring.
    assert (((u * a) * z) mod p = z mod p).
    { replace (u * a) with (1 - v * p) by lia.
      replace ((1 - v * p) * z) with (z + (-v * z) * p) by ring.
      rewrite Z.mod_add by lia.
      reflexivity. }
    rewrite H.
    apply Z.mod_small; lia. }
  split; [exact Hmap|].
  apply in_residues; [lia|].
  pose proof (Z.mod_pos_bound (u * z) p ltac:(lia)) as Hbound.
  split; [|lia].
  destruct (Z.eq_dec ((u * z) mod p) 0) as [Hzero | Hnz]; [|lia].
  rewrite Hzero in Hmap.
  rewrite Z.mul_0_r in Hmap.
  rewrite Z.mod_0_l in Hmap by lia.
  lia.
Qed.

Lemma residues_mul_permutation : forall p a,
  prime p -> 0 < a < p ->
  Permutation (map (fun x => (a * x) mod p) (residues p)) (residues p).
Proof.
  intros p a Hp Ha.
  pose proof (prime_ge_2 p Hp) as Hp2.
  apply NoDup_Permutation.
  - apply NoDup_map_NoDup_ForallPairs.
    + unfold ForallPairs. intros x y Hx Hy Heq.
      eapply prime_mul_mod_cancel.
      * exact Hp.
      * exact Ha.
      * apply in_residues in Hx; [lia|lia].
      * apply in_residues in Hy; [lia|lia].
      * exact Heq.
    + apply residues_nodup.
  - apply residues_nodup.
  - intros z.
    rewrite in_map_iff.
    split.
    + intros [x [Hz Hx]].
      subst z.
      apply prime_mul_residue_in_residues; auto.
    + intros Hz.
      destruct (prime_mul_residue_preimage p a z Hp Ha Hz) as [x [Hmap Hx]].
      exists x. split; auto.
Qed.

Lemma zprod_permutation : forall l1 l2,
  Permutation l1 l2 -> zprod l1 = zprod l2.
Proof.
  intros l1 l2 Hperm.
  induction Hperm; simpl.
  - reflexivity.
  - rewrite IHHperm. reflexivity.
  - ring.
  - congruence.
Qed.

Lemma zprod_map_mul_mod : forall p a l,
  p <> 0 ->
  zprod (map (fun x => (a * x) mod p) l) mod p =
  (a ^ Z.of_nat (length l) * zprod l) mod p.
Proof.
  intros p a l Hp.
  induction l as [|x xs IH].
  - change (1 mod p = (a ^ 0 * 1) mod p).
    rewrite Z.pow_0_r. ring_simplify. reflexivity.
  - simpl.
    change (Z.pow_pos a (Pos.of_succ_nat (length xs))) with
      (a ^ Z.of_nat (S (length xs))).
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    rewrite <- (Z.mul_mod_idemp_r ((a * x) mod p) (zprod (map (fun x0 : Z => (a * x0) mod p) xs)) p) by exact Hp.
    rewrite IH.
    rewrite <- (Z.mul_mod (a * x) (a ^ Z.of_nat (length xs) * zprod xs) p) by exact Hp.
    replace ((a * x) * (a ^ Z.of_nat (length xs) * zprod xs)) with
      ((a * a ^ Z.of_nat (length xs)) * (x * zprod xs)) by ring.
    reflexivity.
Qed.

Lemma zprod_rel_prime : forall p l,
  (forall x, In x l -> rel_prime p x) ->
  rel_prime p (zprod l).
Proof.
  intros p l Hall.
  induction l as [|x xs IH].
  - simpl. apply rel_prime_sym. apply rel_prime_1.
  - simpl. apply rel_prime_mult.
    + apply Hall. simpl; auto.
    + apply IH. intros y Hy. apply Hall. simpl; auto.
Qed.

Lemma residues_product_rel_prime : forall p,
  prime p -> rel_prime p (zprod (residues p)).
Proof.
  intros p Hp.
  pose proof (prime_ge_2 p Hp) as Hp2.
  apply zprod_rel_prime.
  intros x Hx.
  apply rel_prime_sym.
  destruct Hp as [Hpgt Hall].
  apply Hall.
  apply in_residues in Hx; lia.
Qed.

Lemma mod_eq_divide_sub : forall p x y,
  p <> 0 -> x mod p = y mod p -> (p | x - y).
Proof.
  intros p x y Hp Hxy.
  apply Zmod_divide; [exact Hp|].
  rewrite Zminus_mod.
  rewrite Hxy.
  rewrite Z.sub_diag.
  apply Z.mod_0_l; exact Hp.
Qed.

Lemma divide_sub_mod_eq_one : forall p x,
  p <> 0 -> (p | x - 1) -> x mod p = 1 mod p.
Proof.
  intros p x Hp Hdiv.
  destruct Hdiv as [k Hk].
  replace x with (1 + k * p) by lia.
  rewrite Z.mod_add by exact Hp.
  reflexivity.
Qed.

Lemma residues_length : forall p,
  1 < p -> Z.of_nat (length (residues p)) = p - 1.
Proof.
  intros p Hp.
  unfold residues.
  rewrite length_map, length_seq.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma fermat_little_prime : forall p a,
  prime p -> 0 < a < p ->
  a ^ (p - 1) mod p = 1 mod p.
Proof.
  intros p a Hp Ha.
  pose proof (prime_ge_2 p Hp) as Hp2.
  set (P := zprod (residues p)).
  pose proof (residues_mul_permutation p a Hp Ha) as Hperm.
  pose proof (zprod_permutation _ _ Hperm) as Hprod_eq.
  pose proof (zprod_map_mul_mod p a (residues p) ltac:(lia)) as Hmap_mod.
  rewrite Hprod_eq in Hmap_mod.
  rewrite residues_length in Hmap_mod by lia.
  fold P in Hmap_mod.
  assert (Hmod : (a ^ (p - 1) * P) mod p = P mod p).
  { symmetry. exact Hmap_mod. }
  assert (Hdiv : (p | (a ^ (p - 1) - 1) * P)).
  { replace ((a ^ (p - 1) - 1) * P) with (a ^ (p - 1) * P - P) by ring.
    apply mod_eq_divide_sub; [lia|exact Hmod]. }
  assert (Hrel : rel_prime p P).
  { subst P. apply residues_product_rel_prime. exact Hp. }
  assert (Hdiv' : (p | a ^ (p - 1) - 1)).
  { replace ((a ^ (p - 1) - 1) * P) with (P * (a ^ (p - 1) - 1)) in Hdiv by ring.
    exact (Gauss p P (a ^ (p - 1) - 1) Hdiv Hrel). }
  apply divide_sub_mod_eq_one; [lia|exact Hdiv'].
Qed.

Lemma mod_inv_pow_loop_done_inverse : forall p a result base,
  mod_inv_pow_loop p a result base 0 ->
  mod_inverse_spec p a result.
Proof.
  intros p a result base Hloop.
  unfold mod_inv_pow_loop in Hloop.
  destruct Hloop as [Hp [Ha [Hres [Hbase [Hexp Hsem]]]]].
  unfold mod_inverse_spec.
  repeat split; try lia.
  rewrite Z.pow_0_r in Hsem.
  rewrite Z.mul_1_r in Hsem.
  rewrite <- (Z.mul_mod_idemp_r a result p) by lia.
  rewrite Hsem.
  rewrite (Z.mul_mod_idemp_r a (a ^ (p - 2)) p) by lia.
  replace (a * a ^ (p - 2)) with (a ^ (p - 1)).
  - apply fermat_little_prime; auto.
  - replace (p - 1) with (Z.succ (p - 2)) by lia.
    rewrite Z.pow_succ_r by lia.
    reflexivity.
Qed.

Definition mat_mod (p rows cols : Z) (M : matrix) : Prop :=
  0 < p /\
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    0 <= M i j < p.

Definition vector_mod (p n : Z) (X : vector) : Prop :=
  0 < p /\
  forall i, 0 <= i < n -> 0 <= X i < p.

Definition rep_vector (l : list Z) (n : Z) (X : vector) : Prop :=
  0 <= n /\
  Zlength l = n /\
  forall i, 0 <= i < n -> Znth i l 0 = X i.

Definition vector_from_aug_rhs (M : matrix) (n : Z) : vector :=
  fun i => M i n.

Definition vector_as_col (X : vector) : matrix :=
  fun i _ => X i.

Definition aug_linear_lhs (M : matrix) (X : vector) (i n : Z) : Z :=
  dot_prod M (vector_as_col X) i 0 n.

Definition aug_solution_mod (p n : Z) (M : matrix) (X : vector) : Prop :=
  0 < p /\
  forall i,
    0 <= i < n ->
    (aug_linear_lhs M X i n) mod p = (M i n) mod p.

Definition same_solution_set_mod (p n : Z) (M1 M2 : matrix) : Prop :=
  forall X, aug_solution_mod p n M1 X <-> aug_solution_mod p n M2 X.

Definition rref_prefix_mod (p n k : Z) (M : matrix) : Prop :=
  0 < p /\
  0 <= k <= n /\
  forall r c,
    0 <= r < n ->
    0 <= c < k ->
    M r c = if Z.eq_dec r c then 1 else 0.

Definition gauss_inv (p n k : Z) (M0 M : matrix) : Prop :=
  mat_mod p n (n + 1) M /\
  same_solution_set_mod p n M0 M /\
  rref_prefix_mod p n k M.

Definition gauss_success (p n : Z) (M0 : matrix) (X : vector) : Prop :=
  vector_mod p n X /\
  aug_solution_mod p n M0 X.

Definition matrix_row_swap (M : matrix) (r1 r2 : Z) : matrix :=
  fun i j =>
    if Z.eq_dec i r1 then M r2 j
    else if Z.eq_dec i r2 then M r1 j
    else M i j.

Definition row_swap_prefix
  (l : list Z) (rows cols : Z) (M : matrix) (r1 r2 k : Z) : Prop :=
  0 <= rows /\
  0 <= cols /\
  0 <= k <= cols /\
  Zlength l = rows * cols /\
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    Znth (i * cols + j) l 0 =
      if Z_lt_dec j k then matrix_row_swap M r1 r2 i j else M i j.

Definition matrix_row_scale_mod (p : Z) (M : matrix) (row inv : Z) : matrix :=
  fun i j =>
    if Z.eq_dec i row then (inv * M i j) mod p else M i j.

Definition row_scale_prefix
  (l : list Z) (rows cols : Z) (M : matrix) (p row inv k : Z) : Prop :=
  0 <= rows /\
  0 <= cols /\
  0 <= k <= cols /\
  Zlength l = rows * cols /\
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    Znth (i * cols + j) l 0 =
      if Z_lt_dec j k then matrix_row_scale_mod p M row inv i j else M i j.

Definition matrix_row_elim_mod
  (p : Z) (M : matrix) (pivot target factor : Z) : matrix :=
  fun i j =>
    if Z.eq_dec i target then (M i j - factor * M pivot j) mod p else M i j.

Definition row_elim_prefix
  (l : list Z) (rows cols : Z) (M : matrix)
  (p pivot target factor k : Z) : Prop :=
  0 <= rows /\
  0 <= cols /\
  0 <= k <= cols /\
  Zlength l = rows * cols /\
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    Znth (i * cols + j) l 0 =
      if Z_lt_dec j k then matrix_row_elim_mod p M pivot target factor i j else M i j.

Definition matrix_set_col_from_rhs (M : matrix) (n : Z) : vector :=
  vector_from_aug_rhs M n.

Definition pivot_column_ready (p n k : Z) (M : matrix) : Prop :=
  0 < p /\
  0 <= k < n /\
  M k k = 1 /\
  forall r, 0 <= r < n -> r <> k -> M r k = 0.

Definition gauss_finished_matrix (p n : Z) (M : matrix) : Prop :=
  rref_prefix_mod p n n M.

Definition pivot_search_zero_prefix (n k pivot : Z) (M : matrix) : Prop :=
  0 <= k /\
  k <= pivot /\
  pivot <= n /\
  forall r, k <= r < pivot -> M r k = 0.

Definition pivot_column_prefix_ready (p n k i : Z) (M : matrix) : Prop :=
  0 < p /\
  0 <= k < n /\
  0 <= i <= n /\
  M k k = 1 /\
  forall r, 0 <= r < i -> r <> k -> M r k = 0.

Definition rhs_copy_prefix (l : list Z) (n i : Z) (M : matrix) : Prop :=
  0 <= i <= n /\
  Zlength l = n /\
  forall r, 0 <= r < i -> Znth r l 0 = vector_from_aug_rhs M n r.

Lemma rep_vector_length :
  forall l n X, rep_vector l n X -> Zlength l = n.
Proof.
  intros l n X Hrep. unfold rep_vector in Hrep. tauto.
Qed.

Lemma rep_vector_mod_from_mat_rhs :
  forall p n M,
    mat_mod p n (n + 1) M ->
    vector_mod p n (vector_from_aug_rhs M n).
Proof.
  intros p n M [Hp Hentries].
  unfold vector_mod, vector_from_aug_rhs.
  split; [exact Hp |].
  intros i Hi.
  apply Hentries; lia.
Qed.

Lemma rref_prefix_full_diag :
  forall p n M i,
    rref_prefix_mod p n n M ->
    0 <= i < n ->
    M i i = 1.
Proof.
  intros p n M i [_ [_ Hentry]] Hi.
  specialize (Hentry i i Hi Hi).
  destruct Z.eq_dec; lia.
Qed.

Lemma rref_prefix_full_offdiag :
  forall p n M i j,
    rref_prefix_mod p n n M ->
    0 <= i < n ->
    0 <= j < n ->
    i <> j ->
    M i j = 0.
Proof.
  intros p n M i j [_ [_ Hentry]] Hi Hj Hneq.
  specialize (Hentry i j Hi Hj).
  destruct Z.eq_dec; lia.
Qed.

Lemma mod_inverse_spec_inv_nonzero :
  forall p a inv,
    2 <= p ->
    mod_inverse_spec p a inv ->
    inv <> 0.
Proof.
  intros p a inv Hp Hspec Hinv0.
  unfold mod_inverse_spec in Hspec.
  destruct Hspec as [_ [_ [_ Hmod]]].
  subst inv.
  rewrite Z.mul_0_r in Hmod.
  rewrite Z.mod_0_l in Hmod by lia.
  rewrite Z.mod_small in Hmod by lia.
  lia.
Qed.

Lemma mod_field_scanned_prefix_contradiction :
  forall p a i,
    mod_field p ->
    0 < a < p ->
    i >= p ->
    i <= p ->
    (forall j, 1 <= j /\ j < i -> Z.rem (a * j) p <> Z.rem 1 p) ->
    False.
Proof.
  intros p a i Hfield Ha Hi_ge Hi_le Hscan.
  unfold mod_field in Hfield.
  destruct Hfield as [Hp Hinv].
  destruct (Hinv a Ha) as [inv Hspec].
  assert (Hnonzero : inv <> 0).
  { eapply mod_inverse_spec_inv_nonzero; eauto. }
  unfold mod_inverse_spec in Hspec.
  destruct Hspec as [_ [_ [Hinv_range Hmod]]].
  assert (Hrem : Z.rem (a * inv) p = Z.rem 1 p).
  { rewrite Z.rem_mod_nonneg by nia.
    rewrite Z.rem_mod_nonneg by lia.
    exact Hmod. }
  apply (Hscan inv).
  - lia.
  - exact Hrem.
Qed.

Lemma row_swap_prefix_init :
  forall l rows cols M r1 r2,
    rep_matrix l rows cols M ->
    row_swap_prefix l rows cols M r1 r2 0.
Proof.
  intros l rows cols M r1 r2 Hrep.
  unfold row_swap_prefix.
  pose proof (rep_matrix_shape l rows cols M Hrep) as Hshape.
  pose proof (rep_matrix_length l rows cols M Hrep) as Hlen.
  unfold matrix_shape in Hshape.
  destruct Hshape as [Hrows Hcols].
  repeat split; try lia; try exact Hlen.
  intros i j Hi Hj.
  destruct (Z_lt_dec j 0); [lia |].
  replace (i * cols + j) with (row_major_index cols i j)
    by (unfold row_major_index; lia).
  rewrite (rep_matrix_nth l rows cols M i j Hrep Hi Hj).
  reflexivity.
Qed.

Lemma row_major_index_neq :
  forall cols i j i' j',
    0 <= j < cols ->
    0 <= j' < cols ->
    (i <> i' \/ j <> j') ->
    i * cols + j <> i' * cols + j'.
Proof.
  intros cols i j i' j' Hj Hj' Hneq Heq.
  assert (Hidx :
    row_major_index cols i j = row_major_index cols i' j')
    by (unfold row_major_index; lia).
  destruct (row_major_index_inj cols i j i' j' Hj Hj' Hidx).
  tauto.
Qed.

Lemma row_swap_prefix_update :
  forall l rows cols M r1 r2 k,
    row_swap_prefix l rows cols M r1 r2 k ->
    0 <= r1 < rows ->
    0 <= r2 < rows ->
    0 <= k < cols ->
    row_swap_prefix
      (replace_Znth (r2 * cols + k) (Znth (r1 * cols + k) l 0)
        (replace_Znth (r1 * cols + k) (Znth (r2 * cols + k) l 0) l))
      rows cols M r1 r2 (k + 1).
Proof.
  intros l rows cols M r1 r2 k Hprefix Hr1 Hr2 Hk.
  unfold row_swap_prefix in *.
  destruct Hprefix as [Hrows [Hcols [Hkrange [Hlen Hentry]]]].
  repeat split; try lia.
  - repeat rewrite Zlength_replace_Znth. exact Hlen.
  - intros i j Hi Hj.
    set (idx1 := r1 * cols + k).
    set (idx2 := r2 * cols + k).
    set (idx := i * cols + j).
    assert (Hidx1_range : 0 <= idx1 < Zlength l).
    { subst idx1. rewrite Hlen. nia. }
    assert (Hidx2_range : 0 <= idx2 < Zlength l).
    { subst idx2. rewrite Hlen. nia. }
    assert (Hidx_nonneg : 0 <= idx).
    { subst idx. nia. }
    destruct (Z_lt_dec j (k + 1)) as [Hj_next | Hj_next].
    + assert (Hj_le : j < k \/ j = k) by lia.
      destruct Hj_le as [Hj_old | Hj_eq].
      * assert (Hidx_ne_1 : idx <> idx1).
        { subst idx idx1. apply row_major_index_neq; lia. }
        assert (Hidx_ne_2 : idx <> idx2).
        { subst idx idx2. apply row_major_index_neq; lia. }
        rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_2).
        rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_1).
        replace idx with (i * cols + j) by (subst idx; lia).
        rewrite Hentry by lia.
        destruct (Z_lt_dec j k); [reflexivity | lia].
      * subst j.
        destruct (Z.eq_dec r1 r2) as [Hr12 | Hr12].
        -- subst r2.
           assert (Hidx_eq : idx1 = idx2) by (subst idx1 idx2; lia).
           destruct (Z.eq_dec i r1) as [Hi1 | Hi1].
           ++ subst i.
              replace idx with idx1 by (subst idx idx1; lia).
              rewrite Hidx_eq.
              rewrite Znth_replace_Znth_same by
                (rewrite Zlength_replace_Znth; exact Hidx1_range).
              unfold matrix_row_swap.
              repeat destruct Z.eq_dec; try lia.
              destruct (Z_lt_dec k k); try lia.
              replace idx2 with (r1 * cols + k) by (subst idx2; lia).
              rewrite Hentry by lia.
              destruct (Z_lt_dec k k); try lia.
           ++ assert (Hidx_ne_1 : idx <> idx1).
              { subst idx idx1. apply row_major_index_neq; lia. }
              assert (Hidx_ne_2 : idx <> idx2).
              { subst idx idx2. apply row_major_index_neq; lia. }
              rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_2).
              rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_1).
              unfold matrix_row_swap.
              repeat destruct Z.eq_dec; try lia.
              destruct (Z_lt_dec k k); try lia.
              replace idx with (i * cols + k) by (subst idx; lia).
              rewrite Hentry by lia.
              destruct (Z_lt_dec k k); try lia.
        -- destruct (Z.eq_dec i r1) as [Hi1 | Hi1].
           ++ subst i.
              replace idx with idx1 by (subst idx idx1; lia).
              assert (Hidx1_ne_idx2 : idx1 <> idx2).
              { subst idx1 idx2. apply row_major_index_neq; lia. }
              rewrite Znth_replace_Znth_diff by (try lia; exact Hidx1_ne_idx2).
              rewrite Znth_replace_Znth_same by exact Hidx1_range.
              unfold matrix_row_swap.
              repeat destruct Z.eq_dec; try lia.
              destruct (Z_lt_dec k k); try lia.
              replace idx2 with (r2 * cols + k) by (subst idx2; lia).
              rewrite Hentry by lia.
              destruct (Z_lt_dec k k); try lia.
           ++ destruct (Z.eq_dec i r2) as [Hi2 | Hi2].
              ** subst i.
                 replace idx with idx2 by (subst idx idx2; lia).
                 assert (Hidx2_ne_idx1 : idx2 <> idx1).
                 { subst idx1 idx2. apply row_major_index_neq; lia. }
                 rewrite Znth_replace_Znth_same by
                   (rewrite Zlength_replace_Znth; exact Hidx2_range).
                 unfold matrix_row_swap.
                 repeat destruct Z.eq_dec; try lia.
                 destruct (Z_lt_dec k k); try lia.
                 replace idx1 with (r1 * cols + k) by (subst idx1; lia).
                 rewrite Hentry by lia.
                 destruct (Z_lt_dec k k); try lia.
              ** assert (Hidx_ne_1 : idx <> idx1).
                 { subst idx idx1. apply row_major_index_neq; lia. }
                 assert (Hidx_ne_2 : idx <> idx2).
                 { subst idx idx2. apply row_major_index_neq; lia. }
                 rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_2).
                 rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_1).
                 unfold matrix_row_swap.
                 repeat destruct Z.eq_dec; try lia.
                 destruct (Z_lt_dec k k); try lia.
                 replace idx with (i * cols + k) by (subst idx; lia).
                 rewrite Hentry by lia.
                 destruct (Z_lt_dec k k); try lia.
    + assert (Hj_old : ~ j < k) by lia.
      assert (Hidx_ne_1 : idx <> idx1).
      { subst idx idx1. apply row_major_index_neq; lia. }
      assert (Hidx_ne_2 : idx <> idx2).
      { subst idx idx2. apply row_major_index_neq; lia. }
      rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_2).
      rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_1).
      replace idx with (i * cols + j) by (subst idx; lia).
      rewrite Hentry by lia.
      destruct (Z_lt_dec j k); [lia |].
      destruct (Z_lt_dec j (k + 1)); [lia | reflexivity].
Qed.

Lemma row_swap_prefix_full_rep_matrix :
  forall l rows cols M r1 r2 k,
    row_swap_prefix l rows cols M r1 r2 k ->
    k >= cols ->
    rep_matrix l rows cols (matrix_row_swap M r1 r2).
Proof.
  intros l rows cols M r1 r2 k Hprefix Hk.
  unfold row_swap_prefix in Hprefix.
  destruct Hprefix as [Hrows [Hcols [Hkrange [Hlen Hentry]]]].
  assert (Hk_eq : k = cols) by lia.
  subst k.
  unfold rep_matrix, matrix_shape.
  repeat split; try lia; try exact Hlen.
  intros i j Hi Hj.
  unfold row_major_index.
  rewrite Hentry by lia.
  destruct (Z_lt_dec j cols); [reflexivity | lia].
Qed.

Lemma mod_norm_spec_value :
  forall p x r,
    mod_norm_spec p x r ->
    r = x mod p.
Proof.
  intros p x r Hspec.
  unfold mod_norm_spec, mod_congruent in Hspec.
  destruct Hspec as [Hp [Hr Hmod]].
  rewrite Z.mod_small in Hmod by lia.
  exact Hmod.
Qed.

Lemma row_scale_prefix_init :
  forall l rows cols M p row inv,
    rep_matrix l rows cols M ->
    row_scale_prefix l rows cols M p row inv 0.
Proof.
  intros l rows cols M p row inv Hrep.
  unfold row_scale_prefix.
  pose proof (rep_matrix_shape l rows cols M Hrep) as Hshape.
  pose proof (rep_matrix_length l rows cols M Hrep) as Hlen.
  unfold matrix_shape in Hshape.
  destruct Hshape as [Hrows Hcols].
  repeat split; try lia; try exact Hlen.
  intros i j Hi Hj.
  destruct (Z_lt_dec j 0); [lia |].
  replace (i * cols + j) with (row_major_index cols i j)
    by (unfold row_major_index; lia).
  rewrite (rep_matrix_nth l rows cols M i j Hrep Hi Hj).
  reflexivity.
Qed.

Lemma row_scale_prefix_current_entry_mod_bound :
  forall l rows cols M p row inv k,
    row_scale_prefix l rows cols M p row inv k ->
    mat_mod p rows cols M ->
    0 <= row < rows ->
    0 <= k < cols ->
    0 <= Znth (row * cols + k) l 0 < p.
Proof.
  intros l rows cols M p row inv k Hprefix Hmod Hrow Hk.
  unfold row_scale_prefix in Hprefix.
  destruct Hprefix as [_ [_ [_ [_ Hentry]]]].
  unfold mat_mod in Hmod.
  destruct Hmod as [_ Hmod_entries].
  rewrite (Hentry row k Hrow Hk).
  destruct (Z_lt_dec k k); [lia |].
  apply Hmod_entries; assumption.
Qed.

Lemma z_mul_bound_p32768 :
  forall p x y,
    2 <= p ->
    p <= 32768 ->
    0 <= x < p ->
    0 <= y < p ->
    0 <= x * y <= 1073676289.
Proof.
  intros p x y Hp_low Hp_high Hx Hy.
  nia.
Qed.

Lemma row_scale_prefix_update :
  forall l rows cols M p row inv k retval,
    row_scale_prefix l rows cols M p row inv k ->
    0 <= row < rows ->
    0 <= k < cols ->
    mod_norm_spec p (Znth (row * cols + k) l 0 * inv) retval ->
    row_scale_prefix
      (replace_Znth (row * cols + k) retval l)
      rows cols M p row inv (k + 1).
Proof.
  intros l rows cols M p row inv k retval Hprefix Hrow Hk Hnorm.
  unfold row_scale_prefix in *.
  destruct Hprefix as [Hrows [Hcols [Hkrange [Hlen Hentry]]]].
  repeat split; try lia.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - intros i j Hi Hj.
    set (idx_update := row * cols + k).
    set (idx := i * cols + j).
    assert (Hidx_update_nonneg : 0 <= idx_update).
    { subst idx_update. nia. }
    assert (Hidx_update_range : 0 <= idx_update < Zlength l).
    { subst idx_update. rewrite Hlen. nia. }
    assert (Hidx_nonneg : 0 <= idx).
    { subst idx. nia. }
    destruct (Z_lt_dec j (k + 1)) as [Hj_next | Hj_next].
    + assert (Hj_split : j < k \/ j = k) by lia.
      destruct Hj_split as [Hj_old | Hj_eq].
      * assert (Hidx_ne : idx <> idx_update).
        { subst idx idx_update. apply row_major_index_neq; lia. }
        rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne).
        replace idx with (i * cols + j) by (subst idx; lia).
        rewrite Hentry by lia.
        destruct (Z_lt_dec j k); [reflexivity | lia].
      * subst j.
        destruct (Z.eq_dec i row) as [Hi_row | Hi_not_row].
        -- subst i.
           replace idx with idx_update by (subst idx idx_update; lia).
           rewrite Znth_replace_Znth_same by exact Hidx_update_range.
           unfold matrix_row_scale_mod.
           destruct (Z.eq_dec row row); [| lia].
           destruct (Z_lt_dec k (k + 1)); [| lia].
           rewrite (mod_norm_spec_value p (Znth (row * cols + k) l 0 * inv) retval Hnorm).
           replace (Znth (row * cols + k) l 0) with (M row k).
           ++ rewrite Z.mul_comm. reflexivity.
           ++ specialize (Hentry row k Hrow Hk).
              rewrite Hentry.
              destruct (Z_lt_dec k k); [lia | reflexivity].
        -- assert (Hidx_ne : idx <> idx_update).
           { subst idx idx_update. apply row_major_index_neq; lia. }
           rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne).
           replace idx with (i * cols + k) by (subst idx; lia).
           rewrite Hentry by lia.
           unfold matrix_row_scale_mod.
           repeat destruct Z.eq_dec; try lia.
           destruct (Z_lt_dec k k); [lia | reflexivity].
    + assert (Hidx_ne : idx <> idx_update).
      { subst idx idx_update. apply row_major_index_neq; lia. }
      rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne).
      replace idx with (i * cols + j) by (subst idx; lia).
      rewrite Hentry by lia.
      destruct (Z_lt_dec j k); [lia |].
      destruct (Z_lt_dec j (k + 1)); [lia | reflexivity].
Qed.

Lemma row_scale_prefix_full_rep_matrix :
  forall l rows cols M p row inv k,
    row_scale_prefix l rows cols M p row inv k ->
    k >= cols ->
    rep_matrix l rows cols (matrix_row_scale_mod p M row inv).
Proof.
  intros l rows cols M p row inv k Hprefix Hk.
  unfold row_scale_prefix in Hprefix.
  destruct Hprefix as [Hrows [Hcols [Hkrange [Hlen Hentry]]]].
  assert (Hk_eq : k = cols) by lia.
  subst k.
  unfold rep_matrix, matrix_shape.
  repeat split; try lia; try exact Hlen.
  intros i j Hi Hj.
  unfold row_major_index.
  rewrite Hentry by lia.
  destruct (Z_lt_dec j cols); [reflexivity | lia].
Qed.

Lemma matrix_row_scale_mod_mat_mod :
  forall p rows cols M row inv,
    mat_mod p rows cols M ->
    0 <= inv < p ->
    mat_mod p rows cols (matrix_row_scale_mod p M row inv).
Proof.
  intros p rows cols M row inv Hmod Hinv.
  unfold mat_mod in *.
  destruct Hmod as [Hp Hentry].
  split; [exact Hp |].
  intros i j Hi Hj.
  unfold matrix_row_scale_mod.
  destruct (Z.eq_dec i row).
  - apply Z.mod_pos_bound. lia.
  - apply Hentry; assumption.
Qed.

Lemma row_elim_prefix_init :
  forall l rows cols M p pivot target factor,
    rep_matrix l rows cols M ->
    row_elim_prefix l rows cols M p pivot target factor 0.
Proof.
  intros l rows cols M p pivot target factor Hrep.
  unfold row_elim_prefix.
  pose proof (rep_matrix_shape l rows cols M Hrep) as Hshape.
  pose proof (rep_matrix_length l rows cols M Hrep) as Hlen.
  unfold matrix_shape in Hshape.
  destruct Hshape as [Hrows Hcols].
  repeat split; try lia; try exact Hlen.
  intros i j Hi Hj.
  destruct (Z_lt_dec j 0); [lia |].
  replace (i * cols + j) with (row_major_index cols i j)
    by (unfold row_major_index; lia).
  rewrite (rep_matrix_nth l rows cols M i j Hrep Hi Hj).
  reflexivity.
Qed.

Lemma row_elim_prefix_current_entry_mod_bound :
  forall l rows cols M p pivot target factor k i,
    row_elim_prefix l rows cols M p pivot target factor k ->
    mat_mod p rows cols M ->
    0 <= i < rows ->
    0 <= k < cols ->
    0 <= Znth (i * cols + k) l 0 < p.
Proof.
  intros l rows cols M p pivot target factor k i Hprefix Hmod Hi Hk.
  unfold row_elim_prefix in Hprefix.
  destruct Hprefix as [_ [_ [_ [_ Hentry]]]].
  unfold mat_mod in Hmod.
  destruct Hmod as [_ Hmod_entries].
  rewrite (Hentry i k Hi Hk).
  destruct (Z_lt_dec k k); [lia |].
  apply Hmod_entries; assumption.
Qed.

Lemma z_sub_mul_bound_p32768 :
  forall p x y f,
    2 <= p ->
    p <= 32768 ->
    0 <= x < p ->
    0 <= y < p ->
    0 <= f < p ->
    -1073676289 <= x - f * y <= 32767.
Proof.
  intros p x y f Hp_low Hp_high Hx Hy Hf.
  pose proof (z_mul_bound_p32768 p f y Hp_low Hp_high Hf Hy) as Hmul.
  nia.
Qed.

Lemma row_elim_prefix_update :
  forall l rows cols M p pivot target factor k retval,
    row_elim_prefix l rows cols M p pivot target factor k ->
    0 <= pivot < rows ->
    0 <= target < rows ->
    pivot <> target ->
    0 <= k < cols ->
    mod_norm_spec p
      (Znth (target * cols + k) l 0 -
       factor * Znth (pivot * cols + k) l 0) retval ->
    row_elim_prefix
      (replace_Znth (target * cols + k) retval l)
      rows cols M p pivot target factor (k + 1).
Proof.
  intros l rows cols M p pivot target factor k retval
    Hprefix Hpivot Htarget Hpiv_tgt Hk Hnorm.
  unfold row_elim_prefix in *.
  destruct Hprefix as [Hrows [Hcols [Hkrange [Hlen Hentry]]]].
  repeat split; try lia.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - intros i j Hi Hj.
    set (idx_update := target * cols + k).
    set (idx := i * cols + j).
    assert (Hidx_update_range : 0 <= idx_update < Zlength l).
    { subst idx_update. rewrite Hlen. nia. }
    assert (Hidx_nonneg : 0 <= idx).
    { subst idx. nia. }
    destruct (Z_lt_dec j (k + 1)) as [Hj_next | Hj_next].
    + assert (Hj_split : j < k \/ j = k) by lia.
      destruct Hj_split as [Hj_old | Hj_eq].
      * assert (Hidx_ne : idx <> idx_update).
        { subst idx idx_update. apply row_major_index_neq; lia. }
        rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne).
        replace idx with (i * cols + j) by (subst idx; lia).
        rewrite Hentry by lia.
        destruct (Z_lt_dec j k); [reflexivity | lia].
      * subst j.
        destruct (Z.eq_dec i target) as [Hi_target | Hi_not_target].
        -- subst i.
           replace idx with idx_update by (subst idx idx_update; lia).
           rewrite Znth_replace_Znth_same by exact Hidx_update_range.
           unfold matrix_row_elim_mod.
           destruct (Z.eq_dec target target); [| lia].
           destruct (Z_lt_dec k (k + 1)); [| lia].
           rewrite (mod_norm_spec_value p
             (Znth (target * cols + k) l 0 -
              factor * Znth (pivot * cols + k) l 0) retval Hnorm).
           replace (Znth (target * cols + k) l 0) with (M target k).
           replace (Znth (pivot * cols + k) l 0) with (M pivot k).
           ++ reflexivity.
           ++ specialize (Hentry pivot k Hpivot Hk).
              rewrite Hentry.
              destruct (Z_lt_dec k k); [lia | reflexivity].
           ++ specialize (Hentry target k Htarget Hk).
              rewrite Hentry.
              destruct (Z_lt_dec k k); [lia | reflexivity].
        -- assert (Hidx_ne : idx <> idx_update).
           { subst idx idx_update. apply row_major_index_neq; lia. }
           rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne).
           replace idx with (i * cols + k) by (subst idx; lia).
           rewrite Hentry by lia.
           unfold matrix_row_elim_mod.
           repeat destruct Z.eq_dec; try lia.
           destruct (Z_lt_dec k k); [lia | reflexivity].
    + assert (Hidx_ne : idx <> idx_update).
      { subst idx idx_update. apply row_major_index_neq; lia. }
      rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne).
      replace idx with (i * cols + j) by (subst idx; lia).
      rewrite Hentry by lia.
      destruct (Z_lt_dec j k); [lia |].
      destruct (Z_lt_dec j (k + 1)); [lia | reflexivity].
Qed.

Lemma row_elim_prefix_full_rep_matrix :
  forall l rows cols M p pivot target factor k,
    row_elim_prefix l rows cols M p pivot target factor k ->
    k >= cols ->
    rep_matrix l rows cols (matrix_row_elim_mod p M pivot target factor).
Proof.
  intros l rows cols M p pivot target factor k Hprefix Hk.
  unfold row_elim_prefix in Hprefix.
  destruct Hprefix as [Hrows [Hcols [Hkrange [Hlen Hentry]]]].
  assert (Hk_eq : k = cols) by lia.
  subst k.
  unfold rep_matrix, matrix_shape.
  repeat split; try lia; try exact Hlen.
  intros i j Hi Hj.
  unfold row_major_index.
  rewrite Hentry by lia.
  destruct (Z_lt_dec j cols); [reflexivity | lia].
Qed.

Lemma matrix_row_elim_mod_mat_mod :
  forall p rows cols M pivot target factor,
    mat_mod p rows cols M ->
    mat_mod p rows cols (matrix_row_elim_mod p M pivot target factor).
Proof.
  intros p rows cols M pivot target factor Hmod.
  unfold mat_mod in *.
  destruct Hmod as [Hp Hentry].
  split; [exact Hp |].
  intros i j Hi Hj.
  unfold matrix_row_elim_mod.
  destruct (Z.eq_dec i target).
  - apply Z.mod_pos_bound. lia.
  - apply Hentry; assumption.
Qed.

Lemma dot_prod_nat_row_eq_on :
  forall cnt A B X row row',
    (forall c, 0 <= c < Z.of_nat cnt -> A row c = B row' c) ->
    dot_prod_nat A X row 0 cnt =
    dot_prod_nat B X row' 0 cnt.
Proof.
  induction cnt; intros A B X row row' Hrow; simpl.
  - reflexivity.
  - rewrite (IHcnt A B X row row').
    + rewrite Hrow by lia. reflexivity.
    + intros c Hc. apply Hrow. lia.
Qed.

Lemma dot_prod_row_eq_on :
  forall A B X row row' n,
    0 <= n ->
    (forall c, 0 <= c < n -> A row c = B row' c) ->
    dot_prod A X row 0 n =
    dot_prod B X row' 0 n.
Proof.
  intros A B X row row' n Hn Hrow.
  unfold dot_prod.
  apply dot_prod_nat_row_eq_on.
  intros c Hc.
  apply Hrow.
  rewrite Z2Nat.id in Hc by lia.
  exact Hc.
Qed.

Lemma matrix_row_swap_mat_mod :
  forall p rows cols M r1 r2,
    mat_mod p rows cols M ->
    0 <= r1 < rows ->
    0 <= r2 < rows ->
    mat_mod p rows cols (matrix_row_swap M r1 r2).
Proof.
  intros p rows cols M r1 r2 Hmod Hr1 Hr2.
  unfold mat_mod in *.
  destruct Hmod as [Hp Hentry].
  split; [exact Hp |].
  intros i j Hi Hj.
  unfold matrix_row_swap.
  repeat destruct Z.eq_dec; subst; try apply Hentry; try lia.
Qed.

Lemma matrix_row_swap_aug_solution_mod :
  forall p n M X r1 r2,
    aug_solution_mod p n M X ->
    0 <= r1 < n ->
    0 <= r2 < n ->
    aug_solution_mod p n (matrix_row_swap M r1 r2) X.
Proof.
  intros p n M X r1 r2 Hsol Hr1 Hr2.
  unfold aug_solution_mod in *.
  destruct Hsol as [Hp Hrow].
  split; [exact Hp |].
  intros i Hi.
  unfold aug_linear_lhs in *.
  unfold matrix_row_swap at 2.
  destruct (Z.eq_dec i r1) as [Hi_r1 | Hi_r1].
  - subst i.
    specialize (Hrow r2 Hr2).
    rewrite (dot_prod_row_eq_on (matrix_row_swap M r1 r2) M
      (vector_as_col X) r1 r2 n) by
      (try lia; intros c Hc; unfold matrix_row_swap; repeat destruct Z.eq_dec; subst; try lia; reflexivity).
    exact Hrow.
  - destruct (Z.eq_dec i r2) as [Hi_r2 | Hi_r2].
    + subst i.
      specialize (Hrow r1 Hr1).
      rewrite (dot_prod_row_eq_on (matrix_row_swap M r1 r2) M
        (vector_as_col X) r2 r1 n) by
        (try lia; intros c Hc; unfold matrix_row_swap; repeat destruct Z.eq_dec; subst; try lia; reflexivity).
      exact Hrow.
    + specialize (Hrow i Hi).
      rewrite (dot_prod_row_eq_on (matrix_row_swap M r1 r2) M
        (vector_as_col X) i i n) by
        (try lia; intros c Hc; unfold matrix_row_swap; repeat destruct Z.eq_dec; subst; try lia; reflexivity).
      exact Hrow.
Qed.

Lemma matrix_row_swap_same_solution_set :
  forall p n M r1 r2,
    0 <= r1 < n ->
    0 <= r2 < n ->
    same_solution_set_mod p n M (matrix_row_swap M r1 r2).
Proof.
  intros p n M r1 r2 Hr1 Hr2 X.
  split.
  - intro Hsol.
    apply matrix_row_swap_aug_solution_mod; assumption.
  - intro Hsol.
    unfold aug_solution_mod in *.
    destruct Hsol as [Hp Hrow].
    split; [exact Hp |].
    intros i Hi.
    unfold aug_linear_lhs in *.
    destruct (Z.eq_dec i r1) as [Hi_r1 | Hi_r1].
    + subst i.
      specialize (Hrow r2 Hr2).
      rewrite (dot_prod_row_eq_on M (matrix_row_swap M r1 r2)
        (vector_as_col X) r1 r2 n) by
        (try lia; intros c Hc; unfold matrix_row_swap; repeat destruct Z.eq_dec; subst; try lia; reflexivity).
      unfold matrix_row_swap in Hrow.
      repeat destruct Z.eq_dec in Hrow; subst; try lia; try exact Hrow.
    + destruct (Z.eq_dec i r2) as [Hi_r2 | Hi_r2].
      * subst i.
        specialize (Hrow r1 Hr1).
        rewrite (dot_prod_row_eq_on M (matrix_row_swap M r1 r2)
          (vector_as_col X) r2 r1 n) by
          (try lia; intros c Hc; unfold matrix_row_swap; repeat destruct Z.eq_dec; subst; try lia; reflexivity).
        unfold matrix_row_swap in Hrow.
        repeat destruct Z.eq_dec in Hrow; subst; try lia; try exact Hrow.
      * specialize (Hrow i Hi).
        rewrite (dot_prod_row_eq_on M (matrix_row_swap M r1 r2)
          (vector_as_col X) i i n) by
          (try lia; intros c Hc; unfold matrix_row_swap; repeat destruct Z.eq_dec; subst; try lia; reflexivity).
        unfold matrix_row_swap in Hrow.
        repeat destruct Z.eq_dec in Hrow; subst; try lia; try exact Hrow.
Qed.

Lemma matrix_row_swap_rref_prefix_preserve :
  forall p n k pivot M,
    0 <= k < n ->
    k <= pivot ->
    pivot < n ->
    rref_prefix_mod p n k M ->
    pivot_search_zero_prefix n k pivot M ->
    rref_prefix_mod p n k (matrix_row_swap M k pivot).
Proof.
  intros p n k pivot M Hk Hkp Hpn Hrref _.
  unfold rref_prefix_mod in *.
  destruct Hrref as [Hp [Hkrange Hentry]].
  repeat split; try lia.
  intros r c Hr Hc.
  unfold matrix_row_swap.
  destruct (Z.eq_dec r k) as [Hr_k | Hr_k].
  - subst r.
    rewrite Hentry by lia.
    destruct (Z.eq_dec pivot c); destruct (Z.eq_dec k c); lia.
  - destruct (Z.eq_dec r pivot) as [Hr_pivot | Hr_pivot].
    + subst r.
      rewrite Hentry by lia.
      destruct (Z.eq_dec k c); destruct (Z.eq_dec pivot c); lia.
    + rewrite Hentry by lia.
      destruct (Z.eq_dec r c); lia.
Qed.

Lemma row_swap_found_pivot_preserves_gauss :
  forall p n k pivot M0 M,
    0 <= k < n ->
    k <= pivot ->
    pivot < n ->
    gauss_inv p n k M0 M ->
    pivot_search_zero_prefix n k pivot M ->
    gauss_inv p n k M0 (matrix_row_swap M k pivot).
Proof.
  intros p n k pivot M0 M Hk Hkp Hpn Hinv Hprefix.
  unfold gauss_inv in *.
  destruct Hinv as [Hmat [Hsame Hrref]].
  split; [| split].
  - apply matrix_row_swap_mat_mod; try exact Hmat; lia.
  - unfold same_solution_set_mod in *.
    intros X.
    specialize (Hsame X).
    assert (Hpivot_range : 0 <= pivot < n) by lia.
    pose proof (matrix_row_swap_same_solution_set p n M k pivot Hk Hpivot_range X) as Hswap.
    tauto.
  - apply matrix_row_swap_rref_prefix_preserve; assumption.
Qed.

Lemma row_swap_found_pivot_nonzero :
  forall l n cols p k pivot M,
    cols = n + 1 ->
    rep_matrix l n cols M ->
    mat_mod p n cols M ->
    0 <= k < n ->
    k <= pivot ->
    pivot < n ->
    Znth (pivot * cols + k) l 0 <> 0 ->
    0 < matrix_row_swap M k pivot k k < p.
Proof.
  intros l n cols p k pivot M Hcols Hrep Hmod Hk Hkp Hpn Hread.
  assert (Hentry_eq : Znth (pivot * cols + k) l 0 = M pivot k).
  { replace (pivot * cols + k) with (row_major_index cols pivot k)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth l n cols M pivot k Hrep); lia. }
  assert (Hrange : 0 <= M pivot k < p).
  { unfold mat_mod in Hmod.
    destruct Hmod as [_ Hentries].
    apply Hentries; lia. }
  unfold matrix_row_swap.
  destruct (Z.eq_dec k k) as [_ | Hbad]; [| lia].
  rewrite <- Hentry_eq.
  lia.
Qed.

Lemma dot_prod_nat_row_scale_mod_mod :
  forall cnt p M X row inv,
    p <> 0 ->
    (dot_prod_nat
       (matrix_row_scale_mod p M row inv) (vector_as_col X) row 0 cnt) mod p =
    (inv * dot_prod_nat M (vector_as_col X) row 0 cnt) mod p.
Proof.
  induction cnt; intros p M X row inv Hp; simpl.
  - rewrite Z.mul_0_r. rewrite Z.mod_0_l by exact Hp. reflexivity.
  - rewrite Z.add_mod by exact Hp.
    rewrite IHcnt by exact Hp.
    unfold matrix_row_scale_mod, vector_as_col.
    destruct (Z.eq_dec row row) as [_ | Hbad]; [| lia].
    rewrite Z.mul_add_distr_l.
    rewrite Z.add_mod by exact Hp.
    repeat rewrite Z.mul_mod_idemp_l by exact Hp.
    repeat rewrite Z.mul_mod_idemp_r by exact Hp.
    repeat rewrite Z.mod_mod by exact Hp.
    rewrite <- Z.add_mod by exact Hp.
    replace (inv * (M row (Z.of_nat cnt) * X (Z.of_nat cnt)))
      with (inv * M row (Z.of_nat cnt) * X (Z.of_nat cnt)) by ring.
    reflexivity.
Qed.

Lemma dot_prod_row_scale_mod_mod :
  forall p M X row n inv,
    p <> 0 ->
    (dot_prod
       (matrix_row_scale_mod p M row inv) (vector_as_col X) row 0 n) mod p =
    (inv * dot_prod M (vector_as_col X) row 0 n) mod p.
Proof.
  intros p M X row n inv Hp.
  unfold dot_prod.
  apply dot_prod_nat_row_scale_mod_mod.
  exact Hp.
Qed.

Lemma dot_prod_nat_row_scale_mod_other :
  forall cnt p M X i row inv,
    i <> row ->
    dot_prod_nat
      (matrix_row_scale_mod p M row inv) (vector_as_col X) i 0 cnt =
    dot_prod_nat M (vector_as_col X) i 0 cnt.
Proof.
  induction cnt; intros p M X i row inv Hneq; simpl.
  - reflexivity.
  - rewrite IHcnt by exact Hneq.
    unfold matrix_row_scale_mod.
    destruct (Z.eq_dec i row); [lia | reflexivity].
Qed.

Lemma dot_prod_row_scale_mod_other :
  forall p M X i row n inv,
    i <> row ->
    dot_prod
      (matrix_row_scale_mod p M row inv) (vector_as_col X) i 0 n =
    dot_prod M (vector_as_col X) i 0 n.
Proof.
  intros p M X i row n inv Hneq.
  unfold dot_prod.
  apply dot_prod_nat_row_scale_mod_other.
  exact Hneq.
Qed.

Lemma mod_mul_left_inverse_cancel :
  forall p a inv x y,
    1 < p ->
    (a * inv) mod p = 1 mod p ->
    (inv * x) mod p = (inv * y) mod p ->
    x mod p = y mod p.
Proof.
  intros p a inv x y Hp Hainv Hxy.
  assert (Hp0 : p <> 0) by lia.
  assert (Hmul :
    (a * ((inv * x) mod p)) mod p =
    (a * ((inv * y) mod p)) mod p) by now rewrite Hxy.
  rewrite Z.mul_mod_idemp_r in Hmul by exact Hp0.
  rewrite Z.mul_mod_idemp_r in Hmul by exact Hp0.
  replace (a * (inv * x)) with ((a * inv) * x) in Hmul by ring.
  replace (a * (inv * y)) with ((a * inv) * y) in Hmul by ring.
  rewrite <- (Z.mul_mod_idemp_l (a * inv) x p) in Hmul by exact Hp0.
  rewrite <- (Z.mul_mod_idemp_l (a * inv) y p) in Hmul by exact Hp0.
  rewrite Hainv in Hmul.
  replace (1 mod p) with 1 in Hmul by (symmetry; apply Z.mod_small; lia).
  rewrite Z.mul_1_l in Hmul.
  rewrite Z.mul_1_l in Hmul.
  exact Hmul.
Qed.

Lemma matrix_row_scale_mod_aug_solution_mod :
  forall p n M X row inv pv,
    mod_inverse_spec p pv inv ->
    M row row = pv ->
    aug_solution_mod p n M X ->
    0 <= row < n ->
    aug_solution_mod p n (matrix_row_scale_mod p M row inv) X.
Proof.
  intros p n M X row inv pv Hinv Hpv Hsol Hrow.
  unfold mod_inverse_spec in Hinv.
  destruct Hinv as [Hp [_ [_ Hmul]]].
  unfold aug_solution_mod in *.
  destruct Hsol as [_ Hrows].
  split; [exact Hp |].
  intros i Hi.
  unfold aug_linear_lhs.
  unfold matrix_row_scale_mod at 2.
  destruct (Z.eq_dec i row) as [Hirow | Hirow].
  - subst i.
    rewrite dot_prod_row_scale_mod_mod by lia.
    specialize (Hrows row Hrow).
    unfold aug_linear_lhs in Hrows.
    rewrite <- Z.mul_mod_idemp_r by lia.
    rewrite Hrows.
    repeat rewrite Z.mod_mod by lia.
    rewrite Z.mul_mod_idemp_r by lia.
    reflexivity.
  - rewrite dot_prod_row_scale_mod_other by exact Hirow.
    unfold matrix_row_scale_mod.
    destruct (Z.eq_dec i row) as [Hbad | _]; [lia |].
    apply Hrows; exact Hi.
Qed.

Lemma matrix_row_scale_mod_aug_solution_mod_rev :
  forall p n M X row inv pv,
    1 < p ->
    mod_inverse_spec p pv inv ->
    M row row = pv ->
    aug_solution_mod p n (matrix_row_scale_mod p M row inv) X ->
    0 <= row < n ->
    aug_solution_mod p n M X.
Proof.
  intros p n M X row inv pv Hp_strict Hinv Hpv Hsol Hrow.
  unfold mod_inverse_spec in Hinv.
  destruct Hinv as [Hp [_ [_ Hmul]]].
  unfold aug_solution_mod in *.
  destruct Hsol as [_ Hrows].
  split; [exact Hp |].
  intros i Hi.
  destruct (Z.eq_dec i row) as [Hirow | Hirow].
  - subst i.
    specialize (Hrows row Hrow).
    unfold aug_linear_lhs in *.
    rewrite dot_prod_row_scale_mod_mod in Hrows by lia.
    unfold matrix_row_scale_mod at 1 in Hrows.
    destruct (Z.eq_dec row row) as [_ | Hbad]; [| lia].
    rewrite Z.mod_mod in Hrows by lia.
    eapply mod_mul_left_inverse_cancel; eauto; lia.
  - specialize (Hrows i Hi).
    unfold aug_linear_lhs in *.
    rewrite dot_prod_row_scale_mod_other in Hrows by exact Hirow.
    unfold matrix_row_scale_mod in Hrows.
    destruct (Z.eq_dec i row) as [Hbad | _]; [lia |].
    exact Hrows.
Qed.

Lemma matrix_row_scale_mod_same_solution_set :
  forall p n M row inv pv,
    1 < p ->
    mod_inverse_spec p pv inv ->
    M row row = pv ->
    0 <= row < n ->
    same_solution_set_mod p n M (matrix_row_scale_mod p M row inv).
Proof.
  intros p n M row inv pv Hp_strict Hinv Hpv Hrow X.
  split.
  - intro Hsol.
    eapply matrix_row_scale_mod_aug_solution_mod; eauto.
  - intro Hsol.
    eapply matrix_row_scale_mod_aug_solution_mod_rev; eauto.
Qed.

Lemma row_scale_preserves_gauss_inv :
  forall p n k M0 M pv inv,
    1 < p ->
    0 <= k < n ->
    gauss_inv p n k M0 M ->
    M k k = pv ->
    mod_inverse_spec p pv inv ->
    gauss_inv p n k M0 (matrix_row_scale_mod p M k inv).
Proof.
  intros p n k M0 M pv inv Hp_strict Hk Hinv_gauss Hpv Hinv.
  unfold gauss_inv in *.
  destruct Hinv_gauss as [Hmat [Hsame Hrref]].
  unfold mod_inverse_spec in Hinv.
  destruct Hinv as [Hp [Hpv_range [Hinv_range Hmul]]].
  split; [| split].
  - apply matrix_row_scale_mod_mat_mod; try exact Hmat; lia.
  - intros X.
    specialize (Hsame X).
    pose proof (matrix_row_scale_mod_same_solution_set p n M k inv pv
      Hp_strict
      ltac:(unfold mod_inverse_spec; repeat split; try lia; exact Hmul)
      Hpv Hk X) as Hscale.
    tauto.
  - unfold rref_prefix_mod in *.
    destruct Hrref as [Hrref_p [Hkrange Hentry]].
    repeat split; try lia.
    intros r c Hr Hc.
    unfold matrix_row_scale_mod.
    destruct (Z.eq_dec r k) as [Hr_k | Hr_k].
    + subst r.
      assert (c <> k) by lia.
      rewrite Hentry by lia.
      destruct (Z.eq_dec k c) as [Hkc | Hkc]; [lia |].
      rewrite Z.mul_0_r.
      apply Z.mod_0_l.
      lia.
    + rewrite Hentry by lia.
      destruct (Z.eq_dec r c); reflexivity.
Qed.

Lemma row_scale_builds_empty_pivot_prefix :
  forall p n k M pv inv,
    1 < p ->
    0 <= k < n ->
    M k k = pv ->
    mod_inverse_spec p pv inv ->
    pivot_column_prefix_ready p n k 0 (matrix_row_scale_mod p M k inv).
Proof.
  intros p n k M pv inv Hp_strict Hk Hpv Hinv.
  unfold pivot_column_prefix_ready.
  unfold mod_inverse_spec in Hinv.
  destruct Hinv as [Hp [_ [_ Hmul]]].
  repeat split; try lia.
  - unfold matrix_row_scale_mod.
    destruct (Z.eq_dec k k) as [_ | Hbad]; [| lia].
    rewrite Hpv.
    rewrite Z.mul_comm.
    rewrite Hmul.
    apply Z.mod_small; lia.
Qed.

Lemma mod_row_elim_compat :
  forall p a b c d f,
    p <> 0 ->
    a mod p = b mod p ->
    c mod p = d mod p ->
    (a - f * c) mod p = (b - f * d) mod p.
Proof.
  intros p a b c d f Hp Hab Hcd.
  rewrite Zminus_mod.
  rewrite (Zminus_mod b (f * d) p).
  rewrite (Z.mul_mod f c p) by exact Hp.
  rewrite (Z.mul_mod f d p) by exact Hp.
  rewrite Hab.
  rewrite Hcd.
  reflexivity.
Qed.

Lemma mod_row_elim_step_modprod :
  forall p T P a b x f,
    p <> 0 ->
    ((T - f * P) mod p + (((a - f * b) mod p) * x) mod p) mod p =
    ((T + a * x) - f * (P + b * x)) mod p.
Proof.
  intros p T P a b x f Hp.
  rewrite Z.mul_mod_idemp_l by exact Hp.
  rewrite <- Z.add_mod by exact Hp.
  replace ((T - f * P) + (a - f * b) * x)
    with ((T + a * x) - f * (P + b * x)) by ring.
  reflexivity.
Qed.

Lemma mod_row_elim_cancel :
  forall p a b c d f,
    p <> 0 ->
    (a - f * b) mod p = (c - f * d) mod p ->
    b mod p = d mod p ->
    a mod p = c mod p.
Proof.
  intros p a b c d f Hp Helim Hpivot.
  assert (Hadd :
    ((a - f * b) + f * b) mod p =
    ((c - f * d) + f * b) mod p).
  { rewrite (Z.add_mod (a - f * b) (f * b) p) by exact Hp.
    rewrite (Z.add_mod (c - f * d) (f * b) p) by exact Hp.
    rewrite Helim. reflexivity. }
  replace ((a - f * b) + f * b) with a in Hadd by ring.
  replace ((c - f * d) + f * b)
    with (c + f * (b - d)) in Hadd by ring.
  rewrite Hadd.
  rewrite <- Zplus_mod_idemp_r.
  assert (Hterm0 : (f * (b - d)) mod p = 0).
  { rewrite Z.mul_mod by exact Hp.
    replace ((b - d) mod p) with 0.
    - rewrite Z.mul_0_r. apply Z.mod_0_l. exact Hp.
    - rewrite Zminus_mod. rewrite Hpivot.
      replace (d mod p - d mod p) with 0 by ring.
      symmetry. apply Z.mod_0_l. exact Hp. }
  rewrite Hterm0. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma dot_prod_nat_row_elim_mod_mod :
  forall cnt p M X pivot target factor,
    p <> 0 ->
    (dot_prod_nat
       (matrix_row_elim_mod p M pivot target factor)
       (vector_as_col X) target 0 cnt) mod p =
    (dot_prod_nat M (vector_as_col X) target 0 cnt -
     factor * dot_prod_nat M (vector_as_col X) pivot 0 cnt) mod p.
Proof.
  induction cnt; intros p M X pivot target factor Hp; simpl.
  - rewrite Z.mul_0_r. rewrite Z.opp_0. reflexivity.
  - rewrite Z.add_mod by exact Hp.
    rewrite IHcnt by exact Hp.
    unfold matrix_row_elim_mod, vector_as_col.
    destruct (Z.eq_dec target target) as [_ | Hbad]; [| lia].
    apply mod_row_elim_step_modprod.
    exact Hp.
Qed.

Lemma dot_prod_row_elim_mod_mod :
  forall p M X pivot target n factor,
    p <> 0 ->
    (dot_prod
       (matrix_row_elim_mod p M pivot target factor)
       (vector_as_col X) target 0 n) mod p =
    (dot_prod M (vector_as_col X) target 0 n -
     factor * dot_prod M (vector_as_col X) pivot 0 n) mod p.
Proof.
  intros p M X pivot target n factor Hp.
  unfold dot_prod.
  apply dot_prod_nat_row_elim_mod_mod.
  exact Hp.
Qed.

Lemma dot_prod_nat_row_elim_mod_other :
  forall cnt p M X i pivot target factor,
    i <> target ->
    dot_prod_nat
      (matrix_row_elim_mod p M pivot target factor)
      (vector_as_col X) i 0 cnt =
    dot_prod_nat M (vector_as_col X) i 0 cnt.
Proof.
  induction cnt; intros p M X i pivot target factor Hneq; simpl.
  - reflexivity.
  - rewrite IHcnt by exact Hneq.
    unfold matrix_row_elim_mod.
    destruct (Z.eq_dec i target); [lia | reflexivity].
Qed.

Lemma dot_prod_row_elim_mod_other :
  forall p M X i pivot target n factor,
    i <> target ->
    dot_prod
      (matrix_row_elim_mod p M pivot target factor)
      (vector_as_col X) i 0 n =
    dot_prod M (vector_as_col X) i 0 n.
Proof.
  intros p M X i pivot target n factor Hneq.
  unfold dot_prod.
  apply dot_prod_nat_row_elim_mod_other.
  exact Hneq.
Qed.

Lemma matrix_row_elim_mod_aug_solution_mod :
  forall p n M X pivot target factor,
    aug_solution_mod p n M X ->
    0 <= pivot < n ->
    0 <= target < n ->
    aug_solution_mod p n (matrix_row_elim_mod p M pivot target factor) X.
Proof.
  intros p n M X pivot target factor Hsol Hpivot Htarget.
  unfold aug_solution_mod in *.
  destruct Hsol as [Hp Hrows].
  assert (Hp0 : p <> 0) by lia.
  split; [exact Hp |].
  intros r Hr.
  destruct (Z.eq_dec r target) as [Hr_target | Hr_target].
  - subst r.
    specialize (Hrows target Htarget) as Htarget_row.
    specialize (Hrows pivot Hpivot) as Hpivot_row.
    unfold aug_linear_lhs in *.
    rewrite dot_prod_row_elim_mod_mod by exact Hp0.
    unfold matrix_row_elim_mod at 1.
    destruct (Z.eq_dec target target) as [_ | Hbad]; [| lia].
    rewrite Z.mod_mod by exact Hp0.
    apply mod_row_elim_compat; assumption.
  - specialize (Hrows r Hr) as Hrow.
    unfold aug_linear_lhs in *.
    rewrite dot_prod_row_elim_mod_other by exact Hr_target.
    unfold matrix_row_elim_mod.
    destruct (Z.eq_dec r target); [lia | exact Hrow].
Qed.

Lemma matrix_row_elim_mod_aug_solution_mod_rev :
  forall p n M X pivot target factor,
    aug_solution_mod p n (matrix_row_elim_mod p M pivot target factor) X ->
    0 <= pivot < n ->
    0 <= target < n ->
    pivot <> target ->
    aug_solution_mod p n M X.
Proof.
  intros p n M X pivot target factor Hsol Hpivot Htarget Hneq.
  unfold aug_solution_mod in *.
  destruct Hsol as [Hp Hrows].
  assert (Hp0 : p <> 0) by lia.
  split; [exact Hp |].
  intros r Hr.
  destruct (Z.eq_dec r target) as [Hr_target | Hr_target].
  - subst r.
    specialize (Hrows target Htarget) as Helim.
    specialize (Hrows pivot Hpivot) as Hpivot_row.
    unfold aug_linear_lhs in *.
    rewrite dot_prod_row_elim_mod_mod in Helim by exact Hp0.
    unfold matrix_row_elim_mod at 1 in Helim.
    destruct (Z.eq_dec target target) as [_ | Hbad]; [| lia].
    rewrite Z.mod_mod in Helim by exact Hp0.
    assert (Hpivot_orig :
      dot_prod M (vector_as_col X) pivot 0 n mod p =
      M pivot n mod p).
    { rewrite dot_prod_row_elim_mod_other in Hpivot_row by lia.
      unfold matrix_row_elim_mod in Hpivot_row.
      destruct (Z.eq_dec pivot target); [lia | exact Hpivot_row]. }
    eapply mod_row_elim_cancel; eauto.
  - specialize (Hrows r Hr) as Hrow.
    unfold aug_linear_lhs in *.
    rewrite dot_prod_row_elim_mod_other in Hrow by exact Hr_target.
    unfold matrix_row_elim_mod in Hrow.
    destruct (Z.eq_dec r target); [lia | exact Hrow].
Qed.

Lemma matrix_row_elim_mod_same_solution_set :
  forall p n M pivot target factor,
    0 <= pivot < n ->
    0 <= target < n ->
    pivot <> target ->
    same_solution_set_mod p n M
      (matrix_row_elim_mod p M pivot target factor).
Proof.
  intros p n M pivot target factor Hpivot Htarget Hneq X.
  split.
  - intro Hsol.
    eapply matrix_row_elim_mod_aug_solution_mod; eauto.
  - intro Hsol.
    eapply matrix_row_elim_mod_aug_solution_mod_rev; eauto.
Qed.

Lemma row_elim_preserves_gauss_inv :
  forall p n k M0 M target factor,
    0 <= k < n ->
    0 <= target < n ->
    target <> k ->
    gauss_inv p n k M0 M ->
    gauss_inv p n k M0
      (matrix_row_elim_mod p M k target factor).
Proof.
  intros p n k M0 M target factor Hk Htarget Hneq Hinv.
  unfold gauss_inv in *.
  destruct Hinv as [Hmat [Hsame Hrref]].
  split; [| split].
  - apply matrix_row_elim_mod_mat_mod. exact Hmat.
  - intros X.
    specialize (Hsame X).
    pose proof (matrix_row_elim_mod_same_solution_set p n M k target factor
      Hk Htarget ltac:(lia) X) as Helim.
    tauto.
  - unfold rref_prefix_mod in *.
    destruct Hrref as [Hp [Hkrange Hentry]].
    repeat split; try lia.
    intros r c Hr Hc.
    unfold matrix_row_elim_mod.
    destruct (Z.eq_dec r target) as [Hr_target | Hr_target].
    + subst r.
      rewrite Hentry by lia.
      assert (k <> c) by lia.
      rewrite Hentry by lia.
      destruct (Z.eq_dec k c); [lia |].
      destruct (Z.eq_dec target c) as [Htc | Htc].
      * subst c.
        assert (Hp_strict : 1 < p).
        { unfold mat_mod in Hmat.
          destruct Hmat as [_ Hmat_entries].
          pose proof (Hmat_entries target target Htarget ltac:(lia)) as Hrange.
          rewrite Hentry in Hrange by lia.
          destruct (Z.eq_dec target target); lia. }
        rewrite Z.mul_0_r.
        rewrite Z.sub_0_r.
        apply Z.mod_small. lia.
      * rewrite Z.mul_0_r.
        rewrite Z.sub_0_r.
        apply Z.mod_0_l. lia.
    + rewrite Hentry by lia.
      destruct (Z.eq_dec r c); reflexivity.
Qed.

Lemma row_elim_extends_pivot_prefix :
  forall p n k i M factor,
    pivot_column_prefix_ready p n k i M ->
    0 <= i < n ->
    i <> k ->
    M i k = factor ->
    pivot_column_prefix_ready p n k (i + 1)
      (matrix_row_elim_mod p M k i factor).
Proof.
  intros p n k i M factor Hprefix Hi Hneq Hfactor.
  unfold pivot_column_prefix_ready in *.
  destruct Hprefix as [Hp [Hk [Hirange [Hkk Hzero]]]].
  repeat split; try lia.
  - unfold matrix_row_elim_mod.
    destruct (Z.eq_dec k i); [lia | exact Hkk].
  - intros r Hr Hrneq.
    unfold matrix_row_elim_mod.
    destruct (Z.eq_dec r i) as [Hr_i | Hr_i].
    + subst r.
      destruct (Z.eq_dec i i) as [_ | Hbad]; [| lia].
      rewrite Hfactor. rewrite Hkk.
      replace (factor - factor * 1) with 0 by ring.
      apply Z.mod_0_l. lia.
    + destruct (Z.eq_dec r i); [lia |].
      apply Hzero; lia.
Qed.

Lemma pivot_column_prefix_ready_full_to_ready :
  forall p n k i M,
    pivot_column_prefix_ready p n k i M ->
    i >= n ->
    pivot_column_ready p n k M.
Proof.
  intros p n k i M Hprefix Hi_done.
  unfold pivot_column_prefix_ready in Hprefix.
  unfold pivot_column_ready.
  destruct Hprefix as [Hp [Hk [Hi_range [Hkk Hzero]]]].
  repeat split; try lia.
  intros r Hr Hrneq.
  apply Hzero; lia.
Qed.

Lemma rref_prefix_extend_with_ready :
  forall p n k M,
    rref_prefix_mod p n k M ->
    pivot_column_ready p n k M ->
    rref_prefix_mod p n (k + 1) M.
Proof.
  intros p n k M Hrref Hready.
  unfold rref_prefix_mod in *.
  unfold pivot_column_ready in Hready.
  destruct Hrref as [Hp [Hk_range Hentry]].
  destruct Hready as [_ [Hk_strict [Hkk Hzero]]].
  repeat split; try lia.
  intros r c Hr Hc.
  assert (c < k \/ c = k) as [Hc_old | Hc_new] by lia.
  - apply Hentry; lia.
  - subst c.
    destruct (Z.eq_dec r k) as [Hr_eq | Hr_neq].
    + subst r. exact Hkk.
    + apply Hzero; lia.
Qed.

Lemma rhs_copy_prefix_update_from_matrix :
  forall lfin lx n i cols M,
    cols = n + 1 ->
    rep_matrix lfin n cols M ->
    rhs_copy_prefix lx n i M ->
    0 <= i < n ->
    rhs_copy_prefix
      (replace_Znth i (Znth (i * cols + n) lfin 0) lx)
      n (i + 1) M.
Proof.
  intros lfin lx n i cols M Hcols Hrep Hprefix Hi.
  unfold rhs_copy_prefix in *.
  destruct Hprefix as [Hirange [Hlen Hentry]].
  repeat split; try lia.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - intros r Hr.
    assert (r < i \/ r = i) as [Hr_old | Hr_new] by lia.
    + rewrite Znth_replace_Znth_diff by lia.
      apply Hentry. lia.
    + subst r.
      rewrite Znth_replace_Znth_same by (rewrite Hlen; lia).
      unfold vector_from_aug_rhs.
      replace (i * cols + n) with (row_major_index cols i n)
        by (unfold row_major_index; lia).
      rewrite (rep_matrix_nth lfin n cols M i n Hrep) by lia.
      reflexivity.
Qed.

Lemma rhs_copy_prefix_full_rep_vector :
  forall lx n i M,
    i >= n ->
    rhs_copy_prefix lx n i M ->
    rep_vector lx n (vector_from_aug_rhs M n).
Proof.
  intros lx n i M Hi_done Hprefix.
  unfold rhs_copy_prefix in Hprefix.
  destruct Hprefix as [Hirange [Hlen Hentry]].
  unfold rep_vector.
  repeat split; try lia; try exact Hlen.
  intros r Hr.
  apply Hentry. lia.
Qed.

Lemma dot_prod_nat_finished_rhs_eq :
  forall cnt p n M i,
    rref_prefix_mod p n n M ->
    0 <= i < n ->
    Z.of_nat cnt <= n ->
    dot_prod_nat M (vector_as_col (vector_from_aug_rhs M n)) i 0 cnt =
      if Z_lt_dec i (Z.of_nat cnt) then M i n else 0.
Proof.
  induction cnt; intros p n M i Hrref Hi Hcnt; simpl.
  - destruct (Z_lt_dec i 0); lia.
  - rewrite (IHcnt p n M i Hrref Hi) by lia.
    unfold rref_prefix_mod in Hrref.
    destruct Hrref as [Hp [Hnrange Hentry]].
    rewrite (Hentry i (Z.of_nat cnt)) by lia.
    unfold vector_as_col, vector_from_aug_rhs.
    destruct (Z_lt_dec i (Z.of_nat cnt)) as [Hi_old | Hi_not_old].
    + destruct (Z.eq_dec i (Z.of_nat cnt)); [lia |].
      destruct (Z_lt_dec i (Z.pos (Pos.of_succ_nat cnt))); [| lia].
      rewrite Z.mul_0_l. rewrite Z.add_0_r. reflexivity.
    + destruct (Z.eq_dec i (Z.of_nat cnt)) as [Hi_eq | Hi_neq].
      * subst i.
        destruct (Z_lt_dec (Z.of_nat cnt) (Z.pos (Pos.of_succ_nat cnt))); [| lia].
        rewrite Z.mul_1_l. rewrite Z.add_0_l. reflexivity.
      * destruct (Z_lt_dec i (Z.pos (Pos.of_succ_nat cnt))); [lia |].
        rewrite Z.mul_0_l. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma rref_finished_rhs_solution :
  forall p n M,
    rref_prefix_mod p n n M ->
    aug_solution_mod p n M (vector_from_aug_rhs M n).
Proof.
  intros p n M Hrref.
  unfold aug_solution_mod.
  unfold rref_prefix_mod in Hrref.
  destruct Hrref as [Hp [Hnrange Hentry]].
  split; [exact Hp |].
  intros i Hi.
  unfold aug_linear_lhs, dot_prod.
  rewrite dot_prod_nat_finished_rhs_eq with (p := p) (n := n) by
    (try lia; unfold rref_prefix_mod; repeat split; try lia; exact Hentry).
  rewrite Z2Nat.id by lia.
  destruct (Z_lt_dec i n); [reflexivity | lia].
Qed.

Lemma gauss_finished_success_from_rhs_copy :
  forall p n M0 M lx i,
    i >= n ->
    gauss_inv p n n M0 M ->
    gauss_finished_matrix p n M ->
    rhs_copy_prefix lx n i M ->
    rep_vector lx n (vector_from_aug_rhs M n) /\
    gauss_success p n M0 (vector_from_aug_rhs M n).
Proof.
  intros p n M0 M lx i Hi_done Hgauss Hfinished Hprefix.
  assert (Hrep_vec :
    rep_vector lx n (vector_from_aug_rhs M n)).
  { eapply rhs_copy_prefix_full_rep_vector; eauto. }
  split; [exact Hrep_vec |].
  unfold gauss_inv in Hgauss.
  destruct Hgauss as [Hmat [Hsame Hrref]].
  unfold gauss_success.
  split.
  - apply rep_vector_mod_from_mat_rhs. exact Hmat.
  - unfold gauss_finished_matrix in Hfinished.
    pose proof (rref_finished_rhs_solution p n M Hfinished) as Hsol_fin.
    specialize (Hsame (vector_from_aug_rhs M n)).
    apply (proj2 Hsame). exact Hsol_fin.
Qed.
