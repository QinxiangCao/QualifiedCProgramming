#include "fme_ge_gmp/ge/ge_def.h"

void mpz_set(mpz_t rop, const mpz_t op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure store_Z(rop, z) * store_Z(op, z)
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
*/
{
    int i = 0;

    /*@ Inv Assert
          x != 0 && inv != 0 && x != inv &&
          x == x@pre && inv == inv@pre &&
          n == n@pre && col == col@pre &&
          0 <= n && n <= 256 &&
          0 <= n * n && n * n <= INT_MAX &&
          0 <= col && col < n &&
          0 <= i && i <= n &&
          (i >= n || (0 <= i * n + col && i * n + col < n * n)) &&
          (i >= n || (0 <= i && i < n)) &&
          (i >= n || (INT_MIN <= i * n + col && i * n + col <= INT_MAX)) &&
          rep_vector(lx, n, X) &&
          exists linv_cur,
            partial_rep_matrix_col_copy(linv_cur, n, col, i, B, X) &&
            mpz_array(x, n, lx) *
            mpz_array(inv, n * n, linv_cur)
    */
    while (i < n) {
        mpz_set(inv + (i * n + col), x + i) /*@ where (neq) */;
        i = i + 1;
    }
}
