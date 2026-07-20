#include "fme_ge_gmp/ge/ge_def.h"

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
*/;

int build_inverse_cols_gmp(int n, mpz_srcptr p, mpz_ptr a, mpz_ptr inv,
                           mpz_ptr aug, mpz_ptr x)
/*@ low_level_spec
    With A la linv laug lx zp
    Require a != 0 && inv != 0 && aug != 0 && x != 0 && p != 0 &&
            a != inv && a != aug && a != x &&
            inv != aug && inv != x &&
            aug != x &&
            0 <= n && n <= 256 &&
            2 <= zp &&
            prime(zp) &&
            0 <= n * n && n * n <= INT_MAX &&
            0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
            Zlength(linv) == n * n &&
            Zlength(lx) == n &&
            rep_matrix(la, n, n, A) &&
            mat_mod(zp, n, n, A) &&
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
           0 <= __return && __return <= 1 &&
           (__return == 1 =>
             exists Bres,
               rep_matrix(linv2, n, n, Bres) &&
               matrix_inverse_success(zp, n, A, Bres))
*/
{
    int col = 0;

    /*@ Inv Assert
          a != 0 && inv != 0 && aug != 0 && x != 0 && p != 0 &&
          a != inv && a != aug && a != x &&
          inv != aug && inv != x &&
          aug != x &&
          a == a@pre && inv == inv@pre &&
          aug == aug@pre && x == x@pre && p == p@pre &&
          n == n@pre &&
          0 <= n && n <= 256 &&
          2 <= zp &&
          prime(zp) &&
          0 <= n * n && n * n <= INT_MAX &&
          0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
          0 <= col && col <= n &&
          rep_matrix(la, n, n, A) &&
          mat_mod(zp, n, n, A) &&
          exists Bcur linv_cur laug_cur lx_cur,
            partial_rep_matrix_cols(linv_cur, n, col, Bcur) &&
            inverse_cols_prefix_spec(zp, n, A, Bcur, col) &&
            store_Z(p, zp) *
            mpz_array(a, n * n, la) *
            mpz_array(inv, n * n, linv_cur) *
            mpz_array(aug, n * (n + 1), laug_cur) *
            mpz_array(x, n, lx_cur)
    */
    while (col < n) {
        /*@ Given Bcur linv_cur laug_cur lx_cur */
        if (solve_basis_into_col_gmp(n, p, a, col, inv, aug, x)
                /*@ where (low_level_spec)
                      A = A, B = Bcur, la = la,
                      linv = linv_cur, laug = laug_cur, lx = lx_cur */
                == 0) {
            return 0;
        }
        col = col + 1;
    }

    /*@ Assert
          a != 0 && inv != 0 && aug != 0 && x != 0 && p != 0 &&
          a != inv && a != aug && a != x &&
          inv != aug && inv != x &&
          aug != x &&
          a == a@pre && inv == inv@pre &&
          aug == aug@pre && x == x@pre && p == p@pre &&
          n == n@pre &&
          0 <= n && n <= 256 &&
          2 <= zp &&
          prime(zp) &&
          0 <= n * n && n * n <= INT_MAX &&
          0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
          col == n &&
          rep_matrix(la, n, n, A) &&
          mat_mod(zp, n, n, A) &&
          exists Bfin linv_fin laug_cur lx_cur,
            rep_matrix(linv_fin, n, n, Bfin) &&
            inverse_cols_prefix_spec(zp, n, A, Bfin, n) &&
            matrix_inverse_success(zp, n, A, Bfin) &&
            store_Z(p, zp) *
            mpz_array(a, n * n, la) *
            mpz_array(inv, n * n, linv_fin) *
            mpz_array(aug, n * (n + 1), laug_cur) *
            mpz_array(x, n, lx_cur)
    */
    return 1;
}
