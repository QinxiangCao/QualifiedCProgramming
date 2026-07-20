#include "fme_ge_gmp/gmp/gmp_def.h"

/*@ Import Coq Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib */

/*@ Extern Coq (matrix :: *) */
/*@ Extern Coq (vector :: *) */

/*@ Extern Coq (rep_matrix : list Z -> Z -> Z -> matrix -> Prop)
               (rep_vector : list Z -> Z -> vector -> Prop)
               (prime : Z -> Prop)
               (mat_mod : Z -> Z -> Z -> matrix -> Prop)
               (vector_mod : Z -> Z -> vector -> Prop)
               (mod_field : Z -> Prop)
               (mod_norm_spec : Z -> Z -> Z -> Prop)
               (mod_inverse_spec : Z -> Z -> Z -> Prop)
               (mod_inv_pow_loop : Z -> Z -> Z -> Z -> Z -> Prop)
               (matrix_row_swap : matrix -> Z -> Z -> matrix)
               (matrix_col_swap : matrix -> Z -> Z -> matrix)
               (matrix_transpose : matrix -> matrix)
               (matrix_row_scale_mod : Z -> matrix -> Z -> Z -> matrix)
               (matrix_row_elim_mod : Z -> matrix -> Z -> Z -> Z -> matrix)
               (row_swap_prefix : list Z -> Z -> Z -> matrix -> Z -> Z -> Z -> Prop)
               (col_swap_prefix : list Z -> Z -> Z -> matrix -> Z -> Z -> Z -> Prop)
               (row_scale_prefix : list Z -> Z -> Z -> matrix -> Z -> Z -> Z -> Z -> Prop)
               (row_elim_prefix : list Z -> Z -> Z -> matrix -> Z -> Z -> Z -> Z -> Z -> Prop)
               (rref_prefix_mod : Z -> Z -> Z -> matrix -> Prop)
               (pivot_column_ready : Z -> Z -> Z -> matrix -> Prop)
               (gauss_finished_matrix : Z -> Z -> matrix -> Prop)
               (vector_from_aug_rhs : matrix -> Z -> vector)
               (pivot_search_zero_prefix : Z -> Z -> Z -> matrix -> Prop)
               (pivot_column_prefix_ready : Z -> Z -> Z -> Z -> matrix -> Prop)
               (rhs_copy_prefix : list Z -> Z -> Z -> matrix -> Prop)
               (gauss_inv : Z -> Z -> Z -> matrix -> matrix -> Prop)
               (gauss_success : Z -> Z -> matrix -> vector -> Prop)
               (rank_inv_mod : Z -> Z -> Z -> matrix -> matrix -> Prop)
               (rank_mod_success : Z -> Z -> matrix -> Z -> matrix -> Prop)
               (search_submatrix_zero_prefix_mod : Z -> Z -> Z -> Z -> matrix -> Prop)
               (inverse_cols_prefix_spec : Z -> Z -> matrix -> matrix -> Z -> Prop)
               (matrix_aug_basis : Z -> matrix -> Z -> matrix)
               (matrix_set_col : matrix -> Z -> vector -> matrix)
               (matrix_inverse_success : Z -> Z -> matrix -> matrix -> Prop)
               (matrix_entries_int_range : Z -> Z -> matrix -> Prop)
               (partial_rep_matrix_cols : list Z -> Z -> Z -> matrix -> Prop)
               (partial_rep_matrix_col_copy : list Z -> Z -> Z -> Z -> matrix -> vector -> Prop)
               (partial_rep_matrix : list Z -> Z -> Z -> Z -> matrix -> Prop) */

/*@ Extern Coq (mpz_sizeof : Z)
               (mpz_store : Z -> Z -> Z -> Assertion)
               (mpz_array : Z -> Z -> list Z -> Assertion)
               (mpz_missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion) */

/*@ include strategies "ge_gmp_array.strategies" */
