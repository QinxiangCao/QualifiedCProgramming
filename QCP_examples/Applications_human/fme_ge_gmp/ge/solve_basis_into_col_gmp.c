#include "fme_ge_gmp/ge/ge_def.h"

void build_aug_basis_gmp(int n, mpz_srcptr p, mpz_ptr a, int col, mpz_ptr aug)
/*@ low_level_spec
    With A la laug zp
    Require a != 0 && aug != 0 && p != 0 && a != aug &&
            0 <= n && n <= 256 &&
            2 <= zp &&
            0 <= n * n && n * n <= INT_MAX &&
            0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
            0 <= col && col < n &&
            rep_matrix(la, n, n, A) &&
            mat_mod(zp, n, n, A) &&
            store_Z(p, zp) *
            mpz_array(a, n * n, la) *
            mpz_array(aug, n * (n + 1), laug)
    Ensure exists laug2,
           rep_matrix(laug2, n, n + 1, matrix_aug_basis(n, A, col)) &&
           mat_mod(zp, n, n + 1, matrix_aug_basis(n, A, col)) &&
           store_Z(p, zp) *
           mpz_array(a, n * n, la) *
           mpz_array(aug, n * (n + 1), laug2)
*/;

int gauss_solve_mod_gmp(int n, mpz_srcptr p, mpz_ptr aug, mpz_ptr x)
/*@ low_level_spec
    With M0 l lx zp
    Require aug != 0 && x != 0 && p != 0 && aug != x &&
            0 <= n && n <= 256 &&
            2 <= zp &&
            prime(zp) &&
            0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
            Zlength(lx) == n &&
            rep_matrix(l, n, n + 1, M0) &&
            mat_mod(zp, n, n + 1, M0) &&
            store_Z(p, zp) *
            mpz_array(aug, n * (n + 1), l) *
            mpz_array(x, n, lx)
    Ensure exists M2 l2 lx2 X,
           rep_matrix(l2, n, n + 1, M2) &&
           store_Z(p, zp) *
           mpz_array(aug, n * (n + 1), l2) *
           mpz_array(x, n, lx2) &&
           ((__return == 1 && rep_vector(lx2, n, X) && gauss_success(zp, n, M0, X)) ||
            (__return == 0))
*/;

void copy_vector_to_col_gmp(int n, mpz_ptr x, int col, mpz_ptr inv)
/*@ low_level_spec
    With B X linv lx
    Require x != 0 && inv != 0 && x != inv &&
            0 <= n && n <= 256 &&
            0 <= n * n && n * n <= INT_MAX &&
            0 <= col && col < n &&
            rep_vector(lx, n, X) &&
            partial_rep_matrix_cols(linv, n, col, B) &&
            mpz_array(x, n, lx) *
            mpz_array(inv, n * n, linv)
    Ensure exists linv2,
           partial_rep_matrix_cols(linv2, n, col + 1, matrix_set_col(B, col, X)) &&
           mpz_array(x, n, lx) *
           mpz_array(inv, n * n, linv2)
*/;

int solve_basis_into_col_gmp(int n, mpz_srcptr p, mpz_ptr a, int col,
                             mpz_ptr inv, mpz_ptr aug, mpz_ptr x)
/*@ low_level_spec
    With A B la linv laug lx zp
    Require a != 0 && inv != 0 && aug != 0 && x != 0 && p != 0 &&
            a != inv && a != aug && a != x &&
            inv != aug && inv != x &&
            aug != x &&
            0 <= n && n <= 256 &&
            2 <= zp &&
            prime(zp) &&
            0 <= n * n && n * n <= INT_MAX &&
            0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
            Zlength(lx) == n &&
            0 <= col && col < n &&
            rep_matrix(la, n, n, A) &&
            mat_mod(zp, n, n, A) &&
            partial_rep_matrix_cols(linv, n, col, B) &&
            inverse_cols_prefix_spec(zp, n, A, B, col) &&
            store_Z(p, zp) *
            mpz_array(a, n * n, la) *
            mpz_array(inv, n * n, linv) *
            mpz_array(aug, n * (n + 1), laug) *
            mpz_array(x, n, lx)
    Ensure exists linv2 laug2 lx2,
           store_Z(p, zp) *
           mpz_array(a, n * n, la) *
           mpz_array(inv, n * n, linv2) *
           mpz_array(aug, n * (n + 1), laug2) *
           mpz_array(x, n, lx2) &&
           ((__return == 1 &&
             exists Inv2,
               partial_rep_matrix_cols(linv2, n, col + 1, Inv2) &&
               inverse_cols_prefix_spec(zp, n, A, Inv2, col + 1)) ||
            (__return == 0 &&
             partial_rep_matrix_cols(linv2, n, col, B)))
*/
{
    build_aug_basis_gmp(n, p, a, col, aug)
        /*@ where (low_level_spec) A = A, la = la, laug = laug */
        ;

    if (gauss_solve_mod_gmp(n, p, aug, x) == 0) {
        return 0;
    }

    /*@ Assert
          a != 0 && inv != 0 && aug != 0 && x != 0 && p != 0 &&
          a != inv && a != aug && a != x &&
          inv != aug && inv != x &&
          aug != x &&
          a == a@pre && inv == inv@pre &&
          aug == aug@pre && x == x@pre && p == p@pre &&
          n == n@pre && col == col@pre &&
          0 <= n && n <= 256 &&
          2 <= zp &&
          prime(zp) &&
          0 <= n * n && n * n <= INT_MAX &&
          0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
          0 <= col && col < n &&
          rep_matrix(la, n, n, A) &&
          mat_mod(zp, n, n, A) &&
          partial_rep_matrix_cols(linv, n, col, B) &&
          inverse_cols_prefix_spec(zp, n, A, B, col) &&
          exists M2 laug2 lx2 X,
            rep_matrix(laug2, n, n + 1, M2) &&
            rep_vector(lx2, n, X) &&
            gauss_success(zp, n, matrix_aug_basis(n, A, col), X) &&
            store_Z(p, zp) *
            mpz_array(a, n * n, la) *
            mpz_array(inv, n * n, linv) *
            mpz_array(aug, n * (n + 1), laug2) *
            mpz_array(x, n, lx2)
    */
    /*@ Given M2 laug2 lx2 X */

    copy_vector_to_col_gmp(n, x, col, inv)
        /*@ where (low_level_spec) B = B, X = X, linv = linv, lx = lx2 */
        ;

    return 1;
}
