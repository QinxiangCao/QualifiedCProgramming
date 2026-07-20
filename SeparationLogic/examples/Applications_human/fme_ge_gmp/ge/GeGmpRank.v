Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import GeGmpMatrix GeGmpMod.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition matrix_col_swap (M : matrix) (c1 c2 : Z) : matrix :=
  fun i j =>
    if Z.eq_dec j c1 then M i c2
    else if Z.eq_dec j c2 then M i c1
    else M i j.

Definition col_swap_prefix
  (l : list Z) (rows cols : Z) (M : matrix) (c1 c2 k : Z) : Prop :=
  0 <= rows /\
  0 <= cols /\
  0 <= k <= rows /\
  Zlength l = rows * cols /\
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    Znth (i * cols + j) l 0 =
      if Z_lt_dec i k then matrix_col_swap M c1 c2 i j else M i j.

Inductive rank_reachable_mod (p n : Z) (M0 : matrix) : matrix -> Prop :=
| rank_reachable_refl :
    rank_reachable_mod p n M0 M0
| rank_reachable_row_swap :
    forall M r1 r2,
      rank_reachable_mod p n M0 M ->
      0 <= r1 < n ->
      0 <= r2 < n ->
      rank_reachable_mod p n M0 (matrix_row_swap M r1 r2)
| rank_reachable_col_swap :
    forall M c1 c2,
      rank_reachable_mod p n M0 M ->
      0 <= c1 < n ->
      0 <= c2 < n ->
      rank_reachable_mod p n M0 (matrix_col_swap M c1 c2)
| rank_reachable_row_scale :
    forall M row pv inv,
      rank_reachable_mod p n M0 M ->
      0 <= row < n ->
      M row row = pv ->
      mod_inverse_spec p pv inv ->
      rank_reachable_mod p n M0 (matrix_row_scale_mod p M row inv)
| rank_reachable_row_elim :
    forall M pivot target factor,
      rank_reachable_mod p n M0 M ->
      0 <= pivot < n ->
      0 <= target < n ->
      pivot <> target ->
      rank_reachable_mod p n M0
        (matrix_row_elim_mod p M pivot target factor).

Definition rank_inv_mod
  (p n k : Z) (M0 M : matrix) : Prop :=
  mat_mod p n (n + 1) M /\
  rank_reachable_mod p n M0 M /\
  rref_prefix_mod p n k M.

Definition rank_finished_matrix
  (p n k : Z) (M : matrix) : Prop :=
  rref_prefix_mod p n k M /\
  forall i j,
    k <= i < n ->
    k <= j < n ->
    M i j = 0.

Definition rank_mod_success
  (p n : Z) (M0 : matrix) (ret : Z) (M : matrix) : Prop :=
  mat_mod p n (n + 1) M /\
  rank_reachable_mod p n M0 M /\
  rank_finished_matrix p n ret M.

Definition search_submatrix_zero_prefix_mod
  (n k pivot col : Z) (M : matrix) : Prop :=
  k <= pivot <= n /\
  k <= col <= n /\
  (forall r c,
      k <= r < pivot ->
      k <= c < n ->
      M r c = 0) /\
  (pivot < n ->
   forall c,
     k <= c < col ->
     M pivot c = 0).

Lemma col_swap_prefix_init :
  forall l rows cols M c1 c2,
    rep_matrix l rows cols M ->
    col_swap_prefix l rows cols M c1 c2 0.
Proof.
  intros l rows cols M c1 c2 Hrep.
  unfold col_swap_prefix.
  pose proof (rep_matrix_shape l rows cols M Hrep) as Hshape.
  pose proof (rep_matrix_length l rows cols M Hrep) as Hlen.
  unfold matrix_shape in Hshape.
  destruct Hshape as [Hrows Hcols].
  repeat split; try lia; try exact Hlen.
  intros i j Hi Hj.
  destruct (Z_lt_dec i 0); [lia |].
  replace (i * cols + j) with (row_major_index cols i j)
    by (unfold row_major_index; lia).
  rewrite (rep_matrix_nth l rows cols M i j Hrep Hi Hj).
  reflexivity.
Qed.

Lemma col_swap_prefix_update :
  forall l rows cols M c1 c2 k,
    col_swap_prefix l rows cols M c1 c2 k ->
    0 <= c1 < cols ->
    0 <= c2 < cols ->
    0 <= k < rows ->
    col_swap_prefix
      (replace_Znth (k * cols + c2) (Znth (k * cols + c1) l 0)
        (replace_Znth (k * cols + c1) (Znth (k * cols + c2) l 0) l))
      rows cols M c1 c2 (k + 1).
Proof.
  intros l rows cols M c1 c2 k Hprefix Hc1 Hc2 Hk.
  unfold col_swap_prefix in *.
  destruct Hprefix as [Hrows [Hcols [Hkrange [Hlen Hentry]]]].
  repeat split; try lia.
  - repeat rewrite Zlength_replace_Znth. exact Hlen.
  - intros i j Hi Hj.
    set (idx1 := k * cols + c1).
    set (idx2 := k * cols + c2).
    set (idx := i * cols + j).
    assert (Hidx1_range : 0 <= idx1 < Zlength l).
    { subst idx1. rewrite Hlen. nia. }
    assert (Hidx2_range : 0 <= idx2 < Zlength l).
    { subst idx2. rewrite Hlen. nia. }
    destruct (Z_lt_dec i (k + 1)) as [Hi_next | Hi_next].
    + assert (Hi_old_or_eq : i < k \/ i = k) by lia.
      destruct Hi_old_or_eq as [Hi_old | Hi_eq].
      * assert (Hidx_ne_1 : idx <> idx1).
        { subst idx idx1. apply row_major_index_neq; lia. }
        assert (Hidx_ne_2 : idx <> idx2).
        { subst idx idx2. apply row_major_index_neq; lia. }
        rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_2).
        rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_1).
        replace idx with (i * cols + j) by (subst idx; lia).
        rewrite Hentry by lia.
        destruct (Z_lt_dec i k); [reflexivity | lia].
      * subst i.
        destruct (Z.eq_dec c1 c2) as [Hc12 | Hc12].
        -- subst c2.
           assert (Hidx_eq : idx1 = idx2) by (subst idx1 idx2; lia).
           destruct (Z.eq_dec j c1) as [Hj1 | Hj1].
           ++ subst j.
              replace idx with idx1 by (subst idx idx1; lia).
              rewrite Hidx_eq.
              rewrite Znth_replace_Znth_same by
                (rewrite Zlength_replace_Znth; exact Hidx1_range).
              assert (Hzkc1 : Znth idx2 l 0 = M k c1).
              { subst idx2. rewrite Hentry by lia.
                destruct (Z_lt_dec k k); lia. }
              rewrite Hzkc1.
              unfold matrix_col_swap.
              repeat destruct Z.eq_dec; try lia.
           ++ assert (Hidx_ne_1 : idx <> idx1).
              { subst idx idx1. apply row_major_index_neq; lia. }
              assert (Hidx_ne_2 : idx <> idx2).
              { subst idx idx2. apply row_major_index_neq; lia. }
              rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_2).
              rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_1).
              replace idx with (k * cols + j) by (subst idx; lia).
              assert (Hzkj : Znth (k * cols + j) l 0 = M k j).
              { rewrite Hentry by lia.
                destruct (Z_lt_dec k k); lia. }
              rewrite Hzkj.
              unfold matrix_col_swap.
              repeat destruct Z.eq_dec; try lia.
        -- destruct (Z.eq_dec j c1) as [Hj1 | Hj1].
           ++ subst j.
              replace idx with idx1 by (subst idx idx1; lia).
              assert (Hidx1_ne_idx2 : idx1 <> idx2).
              { subst idx1 idx2. apply row_major_index_neq; lia. }
              rewrite Znth_replace_Znth_diff by (try lia; exact Hidx1_ne_idx2).
              rewrite Znth_replace_Znth_same by exact Hidx1_range.
              assert (Hzkc2 : Znth idx2 l 0 = M k c2).
              { subst idx2. rewrite Hentry by lia.
                destruct (Z_lt_dec k k); lia. }
              rewrite Hzkc2.
              unfold matrix_col_swap.
              repeat destruct Z.eq_dec; try lia.
           ++ destruct (Z.eq_dec j c2) as [Hj2 | Hj2].
              ** subst j.
                 replace idx with idx2 by (subst idx idx2; lia).
                 assert (Hidx2_ne_idx1 : idx2 <> idx1).
                 { subst idx1 idx2. apply row_major_index_neq; lia. }
                 rewrite Znth_replace_Znth_same by
                   (rewrite Zlength_replace_Znth; exact Hidx2_range).
                 assert (Hzkc1 : Znth idx1 l 0 = M k c1).
                 { subst idx1. rewrite Hentry by lia.
                   destruct (Z_lt_dec k k); lia. }
                 rewrite Hzkc1.
                 unfold matrix_col_swap.
                 repeat destruct Z.eq_dec; try lia.
              ** assert (Hidx_ne_1 : idx <> idx1).
                 { subst idx idx1. apply row_major_index_neq; lia. }
                 assert (Hidx_ne_2 : idx <> idx2).
                 { subst idx idx2. apply row_major_index_neq; lia. }
                 rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_2).
                 rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_1).
                 replace idx with (k * cols + j) by (subst idx; lia).
                 assert (Hzkj : Znth (k * cols + j) l 0 = M k j).
                 { rewrite Hentry by lia.
                   destruct (Z_lt_dec k k); lia. }
                 rewrite Hzkj.
                 unfold matrix_col_swap.
                 repeat destruct Z.eq_dec; try lia.
    + assert (Hidx_ne_1 : idx <> idx1).
      { subst idx idx1. apply row_major_index_neq; lia. }
      assert (Hidx_ne_2 : idx <> idx2).
      { subst idx idx2. apply row_major_index_neq; lia. }
      rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_2).
      rewrite Znth_replace_Znth_diff by (try lia; exact Hidx_ne_1).
      replace idx with (i * cols + j) by (subst idx; lia).
      rewrite Hentry by lia.
      destruct (Z_lt_dec i k); [lia |].
      destruct (Z_lt_dec i (k + 1)); [lia | reflexivity].
Qed.

Lemma col_swap_prefix_full_rep_matrix :
  forall l rows cols M c1 c2 k,
    col_swap_prefix l rows cols M c1 c2 k ->
    k >= rows ->
    rep_matrix l rows cols (matrix_col_swap M c1 c2).
Proof.
  intros l rows cols M c1 c2 k Hprefix Hk.
  unfold col_swap_prefix in Hprefix.
  destruct Hprefix as [Hrows [Hcols [Hkrange [Hlen Hentry]]]].
  assert (Hk_eq : k = rows) by lia.
  subst k.
  unfold rep_matrix, matrix_shape.
  repeat split; try lia; try exact Hlen.
  intros i j Hi Hj.
  unfold row_major_index.
  rewrite Hentry by lia.
  destruct (Z_lt_dec i rows); [reflexivity | lia].
Qed.

Lemma matrix_col_swap_mat_mod :
  forall p rows cols M c1 c2,
    mat_mod p rows cols M ->
    0 <= c1 < cols ->
    0 <= c2 < cols ->
    mat_mod p rows cols (matrix_col_swap M c1 c2).
Proof.
  intros p rows cols M c1 c2 [Hp Hentry] Hc1 Hc2.
  split; [exact Hp |].
  intros i j Hi Hj.
  unfold matrix_col_swap.
  destruct (Z.eq_dec j c1) as [-> | Hj1].
  - apply Hentry; assumption.
  - destruct (Z.eq_dec j c2) as [-> | Hj2].
    + apply Hentry; assumption.
    + apply Hentry; assumption.
Qed.

Lemma row_swap_preserves_rref_prefix_mod :
  forall p n k M pivot,
    0 <= k < n ->
    k <= pivot < n ->
    rref_prefix_mod p n k M ->
    rref_prefix_mod p n k (matrix_row_swap M k pivot).
Proof.
  intros p n k M pivot Hk Hpivot Hrref.
  unfold rref_prefix_mod in *.
  destruct Hrref as [Hp [Hrange Hentry]].
  repeat split; try lia.
  intros r c Hr Hc.
  unfold matrix_row_swap.
  destruct (Z.eq_dec r k) as [-> | Hr_k].
  - rewrite Hentry by lia.
    destruct (Z.eq_dec pivot c); destruct (Z.eq_dec k c); lia.
  - destruct (Z.eq_dec r pivot) as [-> | Hr_p].
    + rewrite Hentry by lia.
      destruct (Z.eq_dec k c); destruct (Z.eq_dec pivot c); lia.
    + rewrite Hentry by lia.
      destruct (Z.eq_dec r c); lia.
Qed.

Lemma col_swap_preserves_rref_prefix_mod :
  forall p n k M col,
    0 <= k < n ->
    k <= col < n ->
    rref_prefix_mod p n k M ->
    rref_prefix_mod p n k (matrix_col_swap M k col).
Proof.
  intros p n k M col Hk Hcol Hrref.
  unfold rref_prefix_mod in *.
  destruct Hrref as [Hp [Hrange Hentry]].
  repeat split; try lia.
  intros r c Hr Hc.
  unfold matrix_col_swap.
  destruct (Z.eq_dec c k) as [Hck | Hck]; [lia |].
  destruct (Z.eq_dec c col) as [Hccol | Hccol].
  - subst c. lia.
  - rewrite Hentry by lia.
    destruct (Z.eq_dec r c); reflexivity.
Qed.

Lemma row_scale_preserves_rref_prefix_mod :
  forall p n k M inv,
    0 <= k < n ->
    rref_prefix_mod p n k M ->
    rref_prefix_mod p n k (matrix_row_scale_mod p M k inv).
Proof.
  intros p n k M inv Hk Hrref.
  unfold rref_prefix_mod in *.
  destruct Hrref as [Hp [Hrange Hentry]].
  repeat split; try lia.
  intros r c Hr Hc.
  unfold matrix_row_scale_mod.
  destruct (Z.eq_dec r k) as [-> | Hr_k].
  - rewrite Hentry by lia.
    destruct (Z.eq_dec k c); [lia |].
    rewrite Z.mul_0_r.
    apply Z.mod_0_l.
    lia.
  - rewrite Hentry by lia.
    destruct (Z.eq_dec r c); reflexivity.
Qed.

Lemma row_elim_preserves_rref_prefix_mod :
  forall p n k M target factor,
    0 <= k < n ->
    0 <= target < n ->
    target <> k ->
    rref_prefix_mod p n k M ->
    mat_mod p n (n + 1) M ->
    rref_prefix_mod p n k (matrix_row_elim_mod p M k target factor).
Proof.
  intros p n k M target factor Hk Htarget Hneq Hrref Hmat.
  unfold rref_prefix_mod in *.
  destruct Hrref as [Hp [Hrange Hentry]].
  repeat split; try lia.
  intros r c Hr Hc.
  unfold matrix_row_elim_mod.
  destruct (Z.eq_dec r target) as [-> | Hr_t].
  - rewrite Hentry by lia.
    assert (k <> c) by lia.
    rewrite Hentry by lia.
    destruct (Z.eq_dec k c); [lia |].
    destruct (Z.eq_dec target c) as [Htc | Htc].
    + subst c.
      assert (Hp_strict : 1 < p).
      { unfold mat_mod in Hmat.
        destruct Hmat as [_ Hmat_entries].
        pose proof (Hmat_entries target target Htarget ltac:(lia)) as Hrange0.
        rewrite Hentry in Hrange0 by lia.
        destruct (Z.eq_dec target target); lia. }
      rewrite Z.mul_0_r.
      rewrite Z.sub_0_r.
      apply Z.mod_small.
      lia.
    + rewrite Z.mul_0_r.
      rewrite Z.sub_0_r.
      apply Z.mod_0_l.
      lia.
  - rewrite Hentry by lia.
    destruct (Z.eq_dec r c); reflexivity.
Qed.

Lemma row_swap_preserves_rank_inv_mod :
  forall p n k M0 M pivot,
    0 <= k < n ->
    k <= pivot < n ->
    rank_inv_mod p n k M0 M ->
    rank_inv_mod p n k M0 (matrix_row_swap M k pivot).
Proof.
  intros p n k M0 M pivot Hk Hpivot [Hmat [Hreach Hrref]].
  split.
  - apply matrix_row_swap_mat_mod; try exact Hmat; lia.
  - split.
    + eapply rank_reachable_row_swap; eauto; lia.
    + eapply row_swap_preserves_rref_prefix_mod; eauto.
Qed.

Lemma col_swap_preserves_rank_inv_mod :
  forall p n k M0 M col,
    0 <= k < n ->
    k <= col < n ->
    rank_inv_mod p n k M0 M ->
    rank_inv_mod p n k M0 (matrix_col_swap M k col).
Proof.
  intros p n k M0 M col Hk Hcol [Hmat [Hreach Hrref]].
  split.
  - apply matrix_col_swap_mat_mod; try exact Hmat; lia.
  - split.
    + eapply rank_reachable_col_swap; eauto; lia.
    + eapply col_swap_preserves_rref_prefix_mod; eauto.
Qed.

Lemma row_scale_preserves_rank_inv_mod :
  forall p n k M0 M pv inv,
    1 < p ->
    0 <= k < n ->
    rank_inv_mod p n k M0 M ->
    M k k = pv ->
    mod_inverse_spec p pv inv ->
    rank_inv_mod p n k M0 (matrix_row_scale_mod p M k inv).
Proof.
  intros p n k M0 M pv inv Hp_strict Hk [Hmat [Hreach Hrref]] Hpv Hinv.
  unfold mod_inverse_spec in Hinv.
  destruct Hinv as [Hp [Hpv_range [Hinv_range Hmul]]].
  split.
  - apply matrix_row_scale_mod_mat_mod; try exact Hmat; lia.
  - split.
    + eapply rank_reachable_row_scale; eauto.
      unfold mod_inverse_spec.
      repeat split; try lia; exact Hmul.
    + eapply row_scale_preserves_rref_prefix_mod; eauto.
Qed.

Lemma row_elim_preserves_rank_inv_mod :
  forall p n k M0 M target factor,
    0 <= k < n ->
    0 <= target < n ->
    target <> k ->
    rank_inv_mod p n k M0 M ->
    rank_inv_mod p n k M0 (matrix_row_elim_mod p M k target factor).
Proof.
  intros p n k M0 M target factor Hk Htarget Hneq [Hmat [Hreach Hrref]].
  split.
  - apply matrix_row_elim_mod_mat_mod. exact Hmat.
  - split.
    + eapply rank_reachable_row_elim; eauto.
    + eapply row_elim_preserves_rref_prefix_mod; eauto.
Qed.

Lemma search_submatrix_zero_prefix_mod_init :
  forall n k M,
    0 <= k <= n ->
    search_submatrix_zero_prefix_mod n k k k M.
Proof.
  intros n k M Hk.
  unfold search_submatrix_zero_prefix_mod.
  repeat split; intros; lia.
Qed.

Lemma search_submatrix_zero_prefix_mod_col_step :
  forall n k pivot col M,
    search_submatrix_zero_prefix_mod n k pivot col M ->
    pivot < n ->
    col < n ->
    M pivot col = 0 ->
    search_submatrix_zero_prefix_mod n k pivot (col + 1) M.
Proof.
  intros n k pivot col M [Hpivot [Hcol [Hrows Hcur]]] Hpn Hcn Hz.
  unfold search_submatrix_zero_prefix_mod.
  repeat split; try lia.
  - exact Hrows.
  - intros Hpivot_lt c Hc.
    assert (c < col \/ c = col) as [Hcold | ->] by lia.
    + apply Hcur; try lia.
    + exact Hz.
Qed.

Lemma search_submatrix_zero_prefix_mod_row_step :
  forall n k pivot M,
    search_submatrix_zero_prefix_mod n k pivot n M ->
    pivot < n ->
    search_submatrix_zero_prefix_mod n k (pivot + 1) k M.
Proof.
  intros n k pivot M [Hpivot [Hcol [Hrows Hcur]]] Hpn.
  unfold search_submatrix_zero_prefix_mod.
  repeat split; try lia.
  intros r c Hr Hc.
  assert (r < pivot \/ r = pivot) as [Hr_old | ->] by lia.
  - apply Hrows; lia.
  - apply Hcur; lia.
Qed.

Lemma search_submatrix_zero_prefix_mod_done :
  forall n k M,
    search_submatrix_zero_prefix_mod n k n k M ->
    forall i j,
      k <= i < n ->
      k <= j < n ->
      M i j = 0.
Proof.
  intros n k M [Hpivot [_ [Hrows _]]] i j Hi Hj.
  apply Hrows; lia.
Qed.
