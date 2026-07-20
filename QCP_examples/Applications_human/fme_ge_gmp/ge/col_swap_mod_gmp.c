#include "fme_ge_gmp/ge/ge_def.h"

mpz_ptr malloc_mpz_struct()
  /*@ Require emp
      Ensure __return != 0 &&
             undef_data_at(&(__return->_mp_alloc)) *
             undef_data_at(&(__return->_mp_size)) *
             undef_data_at(&(__return->_mp_d))
    */;

void free_mpz_struct(mpz_ptr x)
  /*@ With size cap ptr
      Require x->_mp_size == size &&
              x->_mp_alloc == cap &&
              x->_mp_d == ptr
      Ensure emp
    */;

void mpz_init(mpz_t x)
/*@
  Require
    undef_data_at(&(x->_mp_alloc)) *
    undef_data_at(&(x->_mp_size)) *
    undef_data_at(&(x->_mp_d))
  Ensure
    store_Z(x, 0)
*/;

void mpz_clear(mpz_t r)
/*@
  With
    n
  Require
    store_Z(r, n)
  Ensure
    exists size cap ptr,
      r -> _mp_size == size && r -> _mp_alloc == cap && r -> _mp_d == ptr
*/;

void mpz_set(mpz_t rop, const mpz_t op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure  store_Z(rop, z) * store_Z(op, z)
*/;

void col_swap_mod_gmp(int n, mpz_srcptr p, mpz_ptr aug, int c1, int c2)
/*@ low_level_spec
    With M l zp
    Require aug != 0 &&
            0 <= n && n <= 256 &&
            0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
            0 <= c1 && c1 < n &&
            0 <= c2 && c2 < n &&
            rep_matrix(l, n, n + 1, M) &&
            mat_mod(zp, n, n + 1, M) &&
            store_Z(p, zp) *
            mpz_array(aug, n * (n + 1), l)
    Ensure exists l2,
           rep_matrix(l2, n, n + 1, matrix_col_swap(M, c1, c2)) &&
           mat_mod(zp, n, n + 1, matrix_col_swap(M, c1, c2)) &&
           store_Z(p, zp) *
           mpz_array(aug, n * (n + 1), l2)
*/
{
    int cols = n + 1;
    int i = 0;
    mpz_ptr tmp1;
    mpz_ptr tmp2;

    tmp1 = malloc_mpz_struct();
    mpz_init(tmp1);
    tmp2 = malloc_mpz_struct();
    mpz_init(tmp2);

    /*@ Inv Assert
          exists lcur ztmp1 ztmp2,
            aug != 0 && tmp1 != 0 && tmp2 != 0 &&
            aug == aug@pre &&
            p == p@pre &&
            n == n@pre &&
            c1 == c1@pre &&
            c2 == c2@pre &&
            cols == n + 1 &&
            cols == n@pre + 1 &&
            0 <= n && n <= 256 &&
            0 <= n * cols && n * cols <= INT_MAX &&
            0 <= c1 && c1 < n &&
            0 <= c2 && c2 < n &&
            0 <= i && i <= n &&
            (i >= n || (0 <= i * cols + c1 && i * cols + c1 < n * cols)) &&
            (i >= n || (0 <= i * cols + c2 && i * cols + c2 < n * cols)) &&
            INT_MIN <= i * cols && i * cols <= INT_MAX &&
            INT_MIN <= i * cols + c1 && i * cols + c1 <= INT_MAX &&
            INT_MIN <= i * cols + c2 && i * cols + c2 <= INT_MAX &&
            rep_matrix(l, n, cols, M) &&
            mat_mod(zp, n, cols, M) &&
            col_swap_prefix(lcur, n, cols, M, c1, c2, i) &&
            store_Z(tmp1, ztmp1) *
            store_Z(tmp2, ztmp2) *
            store_Z(p, zp) *
            mpz_array(aug, n * cols, lcur)
    */
    while (i < n) {
        int idx1 = i * cols + c1;
        int idx2 = i * cols + c2;
        mpz_set(tmp1, aug + idx1);
        mpz_set(tmp2, aug + idx2);
        mpz_set(aug + idx1, tmp2);
        /*@ Assert exists lcur lmid,
              aug != 0 && tmp1 != 0 && tmp2 != 0 &&
              aug == aug@pre &&
              p == p@pre &&
              n == n@pre &&
              c1 == c1@pre &&
              c2 == c2@pre &&
              cols == n + 1 &&
              cols == n@pre + 1 &&
              0 <= n && n <= 256 &&
              0 <= n * cols && n * cols <= INT_MAX &&
              0 <= c1 && c1 < n &&
              0 <= c2 && c2 < n &&
              0 <= i && i < n &&
              idx1 == i * cols + c1 &&
              idx2 == i * cols + c2 &&
              0 <= idx1 && idx1 < n * cols &&
              0 <= idx2 && idx2 < n * cols &&
              INT_MIN <= i * cols && i * cols <= INT_MAX &&
              INT_MIN <= idx1 && idx1 <= INT_MAX &&
              INT_MIN <= idx2 && idx2 <= INT_MAX &&
              lmid == replace_Znth(idx1, Znth(idx2, lcur, 0), lcur) &&
              rep_matrix(l, n, cols, M) &&
              mat_mod(zp, n, cols, M) &&
              col_swap_prefix(lcur, n, cols, M, c1, c2, i) &&
              store_Z(tmp1, Znth(idx1, lcur, 0)) *
              store_Z(tmp2, Znth(idx2, lcur, 0)) *
              store_Z(p, zp) *
              mpz_array(aug, n * cols, lmid)
        */
        mpz_set(aug + idx2, tmp1);
        i = i + 1;
    }

    mpz_clear(tmp2);
    free_mpz_struct(tmp2);
    mpz_clear(tmp1);
    free_mpz_struct(tmp1);
}
