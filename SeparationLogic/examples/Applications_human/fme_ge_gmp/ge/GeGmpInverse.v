Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import GeGmpMatrix GeGmpMod.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition basis_vector (k : Z) : vector :=
  fun i => if Z.eq_dec i k then 1 else 0.

Definition matrix_aug_with_vector
  (n : Z) (A : matrix) (X : vector) : matrix :=
  fun i j =>
    if Z.eq_dec j n then X i else A i j.

Definition matrix_aug_basis
  (n : Z) (A : matrix) (k : Z) : matrix :=
  matrix_aug_with_vector n A (basis_vector k).

Definition matrix_row_as_vector
  (M : matrix) (row : Z) : vector :=
  fun j => M row j.

Definition matrix_col_as_vector
  (M : matrix) (col : Z) : vector :=
  fun i => M i col.

Definition matrix_set_row
  (M : matrix) (row : Z) (X : vector) : matrix :=
  fun i j => if Z.eq_dec i row then X j else M i j.

Definition matrix_set_col
  (M : matrix) (col : Z) (X : vector) : matrix :=
  fun i j => if Z.eq_dec j col then X i else M i j.

Definition inverse_rows_prefix_spec
  (p n : Z) (A Rows : matrix) (done : Z) : Prop :=
  0 <= done <= n /\
  forall row,
    0 <= row < done ->
    vector_mod p n (matrix_row_as_vector Rows row) /\
    aug_solution_mod p n (matrix_aug_basis n A row)
      (matrix_row_as_vector Rows row).

Definition inverse_cols_prefix_spec
  (p n : Z) (A Inv : matrix) (done : Z) : Prop :=
  0 <= done <= n /\
  forall col,
    0 <= col < done ->
    vector_mod p n (matrix_col_as_vector Inv col) /\
    aug_solution_mod p n (matrix_aug_basis n A col)
      (matrix_col_as_vector Inv col).

Definition matrix_right_inverse_mod
  (p n : Z) (A B : matrix) : Prop :=
  matrix_congruent_on n n p (matrix_mul A B n) matrix_id.

Definition matrix_inverse_success
  (p n : Z) (A B : matrix) : Prop :=
  mat_mod p n n B /\
  matrix_right_inverse_mod p n A B.

Definition partial_rep_matrix_cols
  (l : list Z) (n done : Z) (M : matrix) : Prop :=
  matrix_shape n n /\
  Zlength l = n * n /\
  0 <= done <= n /\
  forall i j,
    0 <= i < n ->
    0 <= j < done ->
    Znth (row_major_index n i j) l 0 = M i j.

Definition partial_rep_matrix_col_copy
  (l : list Z) (n col done : Z) (M : matrix) (X : vector) : Prop :=
  matrix_shape n n /\
  Zlength l = n * n /\
  0 <= col < n /\
  0 <= done <= n /\
  (forall i j,
     0 <= i < n ->
     0 <= j < col ->
     Znth (row_major_index n i j) l 0 = M i j) /\
  (forall i,
     0 <= i < done ->
     Znth (row_major_index n i col) l 0 = X i).

Lemma rep_vector_nth :
  forall lx n X i,
    rep_vector lx n X ->
    0 <= i < n ->
    Znth i lx 0 = X i.
Proof.
  intros lx n X i Hrep Hi.
  unfold rep_vector in Hrep.
  destruct Hrep as [_ [_ Hnth]].
  apply Hnth; exact Hi.
Qed.

Lemma inverse_rows_prefix_spec_init :
  forall p n A Rows,
    0 <= n ->
    inverse_rows_prefix_spec p n A Rows 0.
Proof.
  intros p n A Rows Hn.
  unfold inverse_rows_prefix_spec.
  split; [lia |].
  intros row Hrow.
  lia.
Qed.

Lemma basis_vector_mod :
  forall p n k,
    2 <= p ->
    vector_mod p n (basis_vector k).
Proof.
  intros p n k Hp.
  unfold vector_mod, basis_vector.
  split; [lia |].
  intros i Hi.
  destruct Z.eq_dec; lia.
Qed.

Lemma matrix_aug_basis_mat_mod :
  forall p n A k,
    2 <= p ->
    mat_mod p n n A ->
    mat_mod p n (n + 1) (matrix_aug_basis n A k).
Proof.
  intros p n A k Hp Hmod.
  unfold mat_mod in *.
  destruct Hmod as [_ Hentry].
  split; [lia |].
  intros i j Hi Hj.
  unfold matrix_aug_basis, matrix_aug_with_vector, basis_vector.
  destruct (Z.eq_dec j n) as [-> | Hjn].
  - destruct Z.eq_dec; lia.
  - assert (0 <= j < n) by lia.
    apply Hentry; assumption.
Qed.

Lemma matrix_row_as_vector_set_row_same :
  forall M row X,
    matrix_row_as_vector (matrix_set_row M row X) row = X.
Proof.
  intros M row X.
  unfold matrix_row_as_vector, matrix_set_row.
  extensionality j.
  destruct Z.eq_dec; congruence.
Qed.

Lemma matrix_row_as_vector_set_row_other :
  forall M row row' X,
    row' <> row ->
    matrix_row_as_vector (matrix_set_row M row X) row' =
    matrix_row_as_vector M row'.
Proof.
  intros M row row' X Hneq.
  unfold matrix_row_as_vector, matrix_set_row.
  extensionality j.
  destruct Z.eq_dec; congruence.
Qed.

Lemma inverse_rows_prefix_spec_extend :
  forall p n A Rows done X,
    inverse_rows_prefix_spec p n A Rows done ->
    0 <= done < n ->
    vector_mod p n X ->
    aug_solution_mod p n (matrix_aug_basis n A done) X ->
    inverse_rows_prefix_spec p n A (matrix_set_row Rows done X) (done + 1).
Proof.
  intros p n A Rows done X [Hdone_range Hprefix] Hdone HX Hsol.
  unfold inverse_rows_prefix_spec.
  split; [lia |].
  intros row Hrow.
  assert (row < done \/ row = done) as [Hlt | Heq] by lia.
  - rewrite matrix_row_as_vector_set_row_other by lia.
    apply Hprefix; lia.
  - subst row.
    rewrite matrix_row_as_vector_set_row_same.
    split; assumption.
Qed.

Lemma inverse_rows_prefix_spec_full_entries_int_range :
  forall p n A Rows,
    p <= INT_MAX ->
    inverse_rows_prefix_spec p n A Rows n ->
    matrix_entries_int_range n n Rows.
Proof.
  intros p n A Rows Hp [Hdone Hprefix] i j Hi Hj.
  destruct (Hprefix i) as [Hvec _]; try lia.
  unfold vector_mod in Hvec.
  destruct Hvec as [_ Hrange].
  specialize (Hrange j Hj).
  unfold matrix_row_as_vector in Hrange.
  lia.
Qed.

Lemma inverse_rows_prefix_spec_full_transpose_mat_mod :
  forall p n A Rows,
    0 < p ->
    inverse_rows_prefix_spec p n A Rows n ->
    mat_mod p n n (matrix_transpose Rows).
Proof.
  intros p n A Rows Hp [Hdone Hprefix].
  split.
  - exact Hp.
  - intros i j Hi Hj.
    destruct (Hprefix j) as [Hvec _]; try lia.
    unfold vector_mod in Hvec.
    destruct Hvec as [_ Hrange].
    specialize (Hrange i Hi).
    unfold matrix_transpose, matrix_row_as_vector in *.
    exact Hrange.
Qed.

Lemma dot_prod_nat_aug_with_vector_lhs :
  forall cnt n A X Y row,
    Z.of_nat cnt <= n ->
    dot_prod_nat (matrix_aug_with_vector n A X) Y row 0 cnt =
    dot_prod_nat A Y row 0 cnt.
Proof.
  induction cnt; intros n A X Y row Hcnt; simpl.
  - reflexivity.
  - rewrite IHcnt by lia.
    unfold matrix_aug_with_vector.
    replace (Z.of_nat cnt) with (Z.of_nat cnt) by reflexivity.
    destruct (Z.eq_dec (Z.of_nat cnt) n); [lia | reflexivity].
Qed.

Lemma aug_linear_lhs_matrix_aug_basis :
  forall n A k X row,
    0 <= n ->
    aug_linear_lhs (matrix_aug_basis n A k) X row n =
    aug_linear_lhs A X row n.
Proof.
  intros n A k X row Hn.
  unfold aug_linear_lhs, dot_prod.
  apply dot_prod_nat_aug_with_vector_lhs.
  rewrite Z2Nat.id by exact Hn.
  lia.
Qed.

Lemma basis_vector_matrix_id :
  forall i j,
    basis_vector j i = matrix_id i j.
Proof.
  intros i j.
  unfold basis_vector, matrix_id.
  destruct (Z.eq_dec i j); destruct (Z.eq_dec i j); lia.
Qed.

Lemma aug_solution_mod_basis_entry :
  forall p n A j X i,
    0 <= n ->
    aug_solution_mod p n (matrix_aug_basis n A j) X ->
    0 <= i < n ->
    (aug_linear_lhs A X i n) mod p = (matrix_id i j) mod p.
Proof.
  intros p n A j X i Hn Hsol Hi.
  unfold aug_solution_mod in Hsol.
  destruct Hsol as [_ Hsol].
  specialize (Hsol i Hi).
  rewrite (aug_linear_lhs_matrix_aug_basis n A j X i Hn) in Hsol.
  unfold matrix_aug_basis, matrix_aug_with_vector in Hsol.
  destruct (Z.eq_dec n n) in Hsol; [| lia].
  rewrite basis_vector_matrix_id in Hsol.
  exact Hsol.
Qed.

Lemma dot_prod_nat_transpose_row :
  forall cnt A Rows i j,
    dot_prod_nat A (matrix_transpose Rows) i j cnt =
    dot_prod_nat
      A (vector_as_col (matrix_row_as_vector Rows j)) i 0 cnt.
Proof.
  induction cnt; intros A Rows i j; simpl.
  - reflexivity.
  - rewrite IHcnt.
    unfold matrix_transpose, vector_as_col, matrix_row_as_vector.
    reflexivity.
Qed.

Lemma dot_prod_transpose_row :
  forall A Rows i j n,
    matrix_mul A (matrix_transpose Rows) n i j =
    aug_linear_lhs A (matrix_row_as_vector Rows j) i n.
Proof.
  intros A Rows i j n.
  unfold matrix_mul, aug_linear_lhs, dot_prod.
  apply dot_prod_nat_transpose_row.
Qed.

Lemma inverse_rows_prefix_spec_full_right_inverse :
  forall p n A Rows,
    inverse_rows_prefix_spec p n A Rows n ->
    matrix_right_inverse_mod p n A (matrix_transpose Rows).
Proof.
  intros p n A Rows Hprefix.
  unfold matrix_right_inverse_mod, matrix_congruent_on.
  intros i j Hi Hj.
  rewrite dot_prod_transpose_row.
  destruct Hprefix as [_ Hrows].
  destruct (Hrows j Hj) as [_ Hsol].
  apply aug_solution_mod_basis_entry; try assumption; lia.
Qed.

Lemma matrix_inverse_success_from_rows :
  forall p n A Rows,
    0 < p ->
    inverse_rows_prefix_spec p n A Rows n ->
    matrix_inverse_success p n A (matrix_transpose Rows).
Proof.
  intros p n A Rows Hp Hprefix.
  unfold matrix_inverse_success.
  split.
  - eapply (inverse_rows_prefix_spec_full_transpose_mat_mod p n A Rows); eauto.
  - eapply (inverse_rows_prefix_spec_full_right_inverse p n A Rows); eauto.
Qed.

Lemma matrix_col_as_vector_set_col_same :
  forall M col X,
    matrix_col_as_vector (matrix_set_col M col X) col = X.
Proof.
  intros M col X.
  unfold matrix_col_as_vector, matrix_set_col.
  extensionality i.
  destruct Z.eq_dec; congruence.
Qed.

Lemma matrix_col_as_vector_set_col_other :
  forall M col col' X,
    col' <> col ->
    matrix_col_as_vector (matrix_set_col M col X) col' =
    matrix_col_as_vector M col'.
Proof.
  intros M col col' X Hneq.
  unfold matrix_col_as_vector, matrix_set_col.
  extensionality i.
  destruct Z.eq_dec; congruence.
Qed.

Lemma inverse_cols_prefix_spec_init :
  forall p n A Inv,
    0 <= n ->
    inverse_cols_prefix_spec p n A Inv 0.
Proof.
  intros p n A Inv Hn.
  unfold inverse_cols_prefix_spec.
  split; [lia |].
  intros col Hcol.
  lia.
Qed.

Lemma inverse_cols_prefix_spec_extend :
  forall p n A Inv done X,
    inverse_cols_prefix_spec p n A Inv done ->
    0 <= done < n ->
    vector_mod p n X ->
    aug_solution_mod p n (matrix_aug_basis n A done) X ->
    inverse_cols_prefix_spec p n A (matrix_set_col Inv done X) (done + 1).
Proof.
  intros p n A Inv done X [Hdone_range Hprefix] Hdone HX Hsol.
  unfold inverse_cols_prefix_spec.
  split; [lia |].
  intros col Hcol.
  assert (col < done \/ col = done) as [Hlt | Heq] by lia.
  - rewrite matrix_col_as_vector_set_col_other by lia.
    apply Hprefix; lia.
  - subst col.
    rewrite matrix_col_as_vector_set_col_same.
    split; assumption.
Qed.

Lemma inverse_cols_prefix_spec_full_entries_int_range :
  forall p n A Inv,
    p <= INT_MAX ->
    inverse_cols_prefix_spec p n A Inv n ->
    matrix_entries_int_range n n Inv.
Proof.
  intros p n A Inv Hp [Hdone Hprefix] i j Hi Hj.
  destruct (Hprefix j) as [Hvec _]; try lia.
  unfold vector_mod in Hvec.
  destruct Hvec as [_ Hrange].
  specialize (Hrange i Hi).
  unfold matrix_col_as_vector in Hrange.
  lia.
Qed.

Lemma inverse_cols_prefix_spec_full_mat_mod :
  forall p n A Inv,
    0 < p ->
    inverse_cols_prefix_spec p n A Inv n ->
    mat_mod p n n Inv.
Proof.
  intros p n A Inv Hp [Hdone Hprefix].
  split; [exact Hp |].
  intros i j Hi Hj.
  destruct (Hprefix j) as [Hvec _]; try lia.
  unfold vector_mod in Hvec.
  destruct Hvec as [_ Hrange].
  specialize (Hrange i Hi).
  unfold matrix_col_as_vector in Hrange.
  exact Hrange.
Qed.

Lemma dot_prod_nat_col_as_vector :
  forall cnt A Inv i j,
    dot_prod_nat A Inv i j cnt =
    dot_prod_nat
      A (vector_as_col (matrix_col_as_vector Inv j)) i 0 cnt.
Proof.
  induction cnt; intros A Inv i j; simpl.
  - reflexivity.
  - rewrite IHcnt.
    unfold vector_as_col, matrix_col_as_vector.
    reflexivity.
Qed.

Lemma dot_prod_col :
  forall A Inv i j n,
    matrix_mul A Inv n i j =
    aug_linear_lhs A (matrix_col_as_vector Inv j) i n.
Proof.
  intros A Inv i j n.
  unfold matrix_mul, aug_linear_lhs, dot_prod.
  apply dot_prod_nat_col_as_vector.
Qed.

Lemma inverse_cols_prefix_spec_full_right_inverse :
  forall p n A Inv,
    inverse_cols_prefix_spec p n A Inv n ->
    matrix_right_inverse_mod p n A Inv.
Proof.
  intros p n A Inv [Hdone Hprefix].
  unfold matrix_right_inverse_mod, matrix_congruent_on.
  intros i j Hi Hj.
  rewrite dot_prod_col.
  destruct (Hprefix j Hj) as [_ Hsol].
  apply aug_solution_mod_basis_entry; try assumption; lia.
Qed.

Lemma matrix_inverse_success_from_cols :
  forall p n A Inv,
    0 < p ->
    inverse_cols_prefix_spec p n A Inv n ->
    matrix_inverse_success p n A Inv.
Proof.
  intros p n A Inv Hp Hprefix.
  unfold matrix_inverse_success.
  split.
  - eapply (inverse_cols_prefix_spec_full_mat_mod p n A Inv); eauto.
  - eapply (inverse_cols_prefix_spec_full_right_inverse p n A Inv); eauto.
Qed.

Lemma partial_rep_matrix_cols_0_from_length :
  forall l n M,
    0 <= n ->
    Zlength l = n * n ->
    partial_rep_matrix_cols l n 0 M.
Proof.
  intros l n M Hn Hlen.
  unfold partial_rep_matrix_cols.
  repeat split; try (unfold matrix_shape; lia); try lia.
Qed.

Lemma partial_rep_matrix_cols_full_rep_matrix :
  forall l n M,
    partial_rep_matrix_cols l n n M ->
    rep_matrix l n n M.
Proof.
  intros l n M Hpart.
  unfold partial_rep_matrix_cols in Hpart.
  destruct Hpart as [Hshape [Hlen [_ Hentry]]].
  unfold rep_matrix.
  split; [exact Hshape |].
  split; [exact Hlen |].
  intros i j Hi Hj.
  apply Hentry; assumption.
Qed.

Lemma partial_rep_matrix_cols_length :
  forall l n done M,
    partial_rep_matrix_cols l n done M ->
    Zlength l = n * n.
Proof.
  intros l n done M Hpart.
  unfold partial_rep_matrix_cols in Hpart.
  tauto.
Qed.

Lemma partial_rep_matrix_cols_done_range :
  forall l n done M,
    partial_rep_matrix_cols l n done M ->
    0 <= done <= n.
Proof.
  intros l n done M Hpart.
  unfold partial_rep_matrix_cols in Hpart.
  tauto.
Qed.

Lemma partial_rep_matrix_col_copy_init :
  forall l n col M X,
    partial_rep_matrix_cols l n col M ->
    0 <= col < n ->
    partial_rep_matrix_col_copy l n col 0 M X.
Proof.
  intros l n col M X Hcols Hcol.
  unfold partial_rep_matrix_cols in Hcols.
  destruct Hcols as [Hshape [Hlen [_ Hentry]]].
  unfold partial_rep_matrix_col_copy.
  split; [exact Hshape |].
  split; [exact Hlen |].
  split; [lia |].
  split; [lia |].
  split.
  - intros i j Hi Hj.
    apply Hentry; assumption.
  - intros i Hi.
    lia.
Qed.

Lemma partial_rep_matrix_col_copy_update_next :
  forall l n col done M X v,
    partial_rep_matrix_col_copy l n col done M X ->
    0 <= done < n ->
    v = X done ->
    partial_rep_matrix_col_copy
      (replace_Znth (row_major_index n done col) v l)
      n col (done + 1) M X.
Proof.
  intros l n col done M X v Hcopy Hdone Hv.
  unfold partial_rep_matrix_col_copy in *.
  destruct Hcopy as
    [Hshape [Hlen [Hcol [Hdone_range [Hprev Hcur]]]]].
  assert (Hn : 0 <= n).
  { unfold matrix_shape in Hshape; lia. }
  assert (Hupdate_bound :
    0 <= row_major_index n done col < n * n).
  { apply row_major_index_bound; lia. }
  repeat split; try exact Hshape; try lia.
  - rewrite Zlength_replace_Znth.
    exact Hlen.
  - intros i j Hi Hj.
    assert (Hidx_bound : 0 <= row_major_index n i j < n * n).
    { apply row_major_index_bound; lia. }
    rewrite Znth_replace_Znth_diff.
    + apply Hprev; assumption.
    + lia.
    + lia.
    + intro Heq.
      assert (Hj_n : 0 <= j < n) by lia.
      destruct (row_major_index_inj n i j done col Hj_n Hcol Heq)
        as [_ Hj_eq].
      lia.
  - intros i Hi.
    destruct (Z.eq_dec i done) as [Heq | Hneq].
    + subst i v.
      rewrite Znth_replace_Znth_same.
      * reflexivity.
      * rewrite Hlen.
        lia.
    + assert (Hidx_bound : 0 <= row_major_index n i col < n * n).
      { apply row_major_index_bound; lia. }
      rewrite Znth_replace_Znth_diff.
      * apply Hcur; lia.
      * lia.
      * lia.
      * intro Heq.
        destruct (row_major_index_inj n i col done col Hcol Hcol Heq)
          as [Hi_eq _].
        lia.
Qed.

Lemma partial_rep_matrix_col_copy_finish :
  forall l n col M X,
    partial_rep_matrix_col_copy l n col n M X ->
    partial_rep_matrix_cols l n (col + 1) (matrix_set_col M col X).
Proof.
  intros l n col M X Hcopy.
  unfold partial_rep_matrix_col_copy in Hcopy.
  destruct Hcopy as
    [Hshape [Hlen [Hcol [Hdone_range [Hprev Hcur]]]]].
  unfold partial_rep_matrix_cols.
  repeat split; try exact Hshape; try exact Hlen; try lia.
  intros i j Hi Hj.
  assert (j < col \/ j = col) as [Hlt | Heq] by lia.
  - rewrite Hprev by lia.
    unfold matrix_set_col.
    destruct Z.eq_dec; [lia | reflexivity].
  - subst j.
    rewrite Hcur by lia.
    unfold matrix_set_col.
    destruct Z.eq_dec; [reflexivity | lia].
Qed.
