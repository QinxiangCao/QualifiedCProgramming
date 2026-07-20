#include "fme_ge_gmp/ge/ge_def.h"

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
*/;

int matrix_inverse_gmp(int n, mpz_srcptr p, mpz_ptr a, mpz_ptr inv,
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
            Zlength(laug) == n * (n + 1) &&
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
           ((__return == 1 &&
             exists Bres,
               rep_matrix(linv2, n, n, Bres) &&
               matrix_inverse_success(zp, n, A, Bres)) ||
            (__return == 0))
*/
{
    if (build_inverse_cols_gmp(n, p, a, inv, aug, x)
            /*@ where (low_level_spec)
                  A = A, la = la, linv = linv,
                  laug = laug, lx = lx */
            != 1) {
        return 0;
    }

    return 1;
}
