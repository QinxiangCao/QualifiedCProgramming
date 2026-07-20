#include "fme_ge_gmp/ge/ge_def.h"

void mpz_set(mpz_t rop, const mpz_t op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure  store_Z(rop, z) * store_Z(op, z)
*/;

void mpz_set_ui(mpz_t r, unsigned long x)
/*@
  With old x0
  Require x == x0 && 0 <= x0 && store_Z(r, old)
  Ensure store_Z(r, x0)
*/;

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
*/
{
    int cols = n + 1;
    int i = 0;
    int idx = 0;

    /*@ Inv Assert
          a != 0 && aug != 0 && p != 0 && a != aug &&
          a == a@pre && aug == aug@pre && p == p@pre &&
          n == n@pre && col == col@pre &&
          cols == n + 1 &&
          cols == n@pre + 1 &&
          0 <= n && n <= 256 &&
          2 <= zp &&
          0 <= n * n && n * n <= INT_MAX &&
          0 <= n * cols && n * cols <= INT_MAX &&
          0 <= col && col < n &&
          0 <= i && i <= n &&
          idx == i * cols &&
          0 <= idx && idx <= n * cols &&
          INT_MIN <= idx && idx <= INT_MAX &&
          rep_matrix(la, n, n, A) &&
          mat_mod(zp, n, n, A) &&
          exists laug_cur,
            partial_rep_matrix(laug_cur, n, cols, idx, matrix_aug_basis(n, A, col)) &&
            store_Z(p, zp) *
            mpz_array(a, n * n, la) *
            mpz_array(aug, n * cols, laug_cur)
    */
    while (i < n) {
        int j = 0;

        /*@ Inv Assert
              a != 0 && aug != 0 && p != 0 && a != aug &&
              a == a@pre && aug == aug@pre && p == p@pre &&
              n == n@pre && col == col@pre &&
              cols == n + 1 &&
              cols == n@pre + 1 &&
              0 <= n && n <= 256 &&
              2 <= zp &&
              0 <= n * n && n * n <= INT_MAX &&
              0 <= n * cols && n * cols <= INT_MAX &&
              0 <= col && col < n &&
              0 <= i && i < n &&
              0 <= j && j <= cols &&
              idx == i * cols + j &&
              0 <= idx && idx <= n * cols &&
              (j >= cols || idx < n * cols) &&
              (j >= n || (0 <= i * n + j && i * n + j < n * n)) &&
              INT_MIN <= i * n + j && i * n + j <= INT_MAX &&
              INT_MIN <= idx && idx <= INT_MAX &&
              rep_matrix(la, n, n, A) &&
              mat_mod(zp, n, n, A) &&
              exists laug_cur,
                partial_rep_matrix(laug_cur, n, cols, idx, matrix_aug_basis(n, A, col)) &&
                store_Z(p, zp) *
                mpz_array(a, n * n, la) *
                mpz_array(aug, n * cols, laug_cur)
        */
        while (j < cols) {
            if (j == n) {
                if (i == col) {
                    mpz_set_ui(aug + idx, 1);
                } else {
                    mpz_set_ui(aug + idx, 0);
                }
            } else {
                mpz_set(aug + idx, a + (i * n + j)) /*@ where (neq) */;
            }
            j = j + 1;
            idx = idx + 1;
        }
        i = i + 1;
    }
}
