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

void mpz_mul(mpz_ptr rop, mpz_srcptr op1, mpz_srcptr op2)
/*@
  With
    old z1 z2
  Require
    store_Z(rop, old) * store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    store_Z(rop, z1 * z2) * store_Z(op1, z1) * store_Z(op2, z2)
*/;

void mpz_sub(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ r_eq_a
  With
    za zb
  Require
    r == a && store_Z(a, za) * store_Z(b, zb)
  Ensure
    store_Z(a, za - zb) * store_Z(b, zb)
*/;

void mod_norm_gmp(mpz_ptr r, mpz_srcptr x, mpz_srcptr p)
/*@ low_level_spec
  With old zx zp
  Require
    r != 0 &&
    zp > 0 &&
    store_Z(r, old) * store_Z(x, zx) * store_Z(p, zp)
  Ensure exists out,
    mod_norm_spec(zp, zx, out) &&
    store_Z(r, out) * store_Z(x, zx) * store_Z(p, zp)
*/;

void row_elim_mod_gmp(int n, mpz_srcptr p, mpz_ptr aug,
                      int pivot, int target, mpz_srcptr factor)
/*@ low_level_spec
    With M l zp zfactor
    Require aug != 0 && p != 0 && factor != 0 &&
            0 <= n && n <= 256 &&
            zp > 0 &&
            0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
            0 <= pivot && pivot < n &&
            0 <= target && target < n &&
            pivot != target &&
            0 <= zfactor && zfactor < zp &&
            rep_matrix(l, n, n + 1, M) &&
            mat_mod(zp, n, n + 1, M) &&
            store_Z(p, zp) *
            store_Z(factor, zfactor) *
            mpz_array(aug, n * (n + 1), l)
    Ensure exists l2,
           rep_matrix(l2, n, n + 1, matrix_row_elim_mod(zp, M, pivot, target, zfactor)) &&
           mat_mod(zp, n, n + 1, matrix_row_elim_mod(zp, M, pivot, target, zfactor)) &&
           store_Z(p, zp) *
           store_Z(factor, zfactor) *
           mpz_array(aug, n * (n + 1), l2)
*/
{
    int cols = n + 1;
    int j = 0;
    mpz_ptr prod;
    mpz_ptr v;

    prod = malloc_mpz_struct();
    mpz_init(prod);
    v = malloc_mpz_struct();
    mpz_init(v);

    /*@ Inv Assert
          exists lcur zprod zv,
            aug != 0 && p != 0 && factor != 0 && prod != 0 && v != 0 &&
            aug == aug@pre &&
            p == p@pre &&
            factor == factor@pre &&
            n == n@pre &&
            pivot == pivot@pre &&
            target == target@pre &&
            cols == n + 1 &&
            cols == n@pre + 1 &&
            0 <= n && n <= 256 &&
            zp > 0 &&
            0 <= n * cols && n * cols <= INT_MAX &&
            0 <= pivot && pivot < n &&
            0 <= target && target < n &&
            pivot != target &&
            0 <= zfactor && zfactor < zp &&
            0 <= j && j <= cols &&
            (j >= cols || (0 <= target * cols + j && target * cols + j < n * cols)) &&
            (j >= cols || (0 <= pivot * cols + j && pivot * cols + j < n * cols)) &&
            INT_MIN <= target * cols && target * cols <= INT_MAX &&
            INT_MIN <= pivot * cols && pivot * cols <= INT_MAX &&
            INT_MIN <= target * cols + j && target * cols + j <= INT_MAX &&
            INT_MIN <= pivot * cols + j && pivot * cols + j <= INT_MAX &&
            rep_matrix(l, n, cols, M) &&
            mat_mod(zp, n, cols, M) &&
            row_elim_prefix(lcur, n, cols, M, zp, pivot, target, zfactor, j) &&
            store_Z(v, zv) *
            store_Z(prod, zprod) *
            store_Z(p, zp) *
            store_Z(factor, zfactor) *
            mpz_array(aug, n * cols, lcur)
    */
    while (j < cols) {
        int idx = target * cols + j;
        int pidx = pivot * cols + j;
        mpz_mul(prod, factor, aug + pidx);
        mpz_set(v, aug + idx);
        mpz_sub(v, v, prod);
        mod_norm_gmp(aug + idx, v, p);
        j = j + 1;
    }

    mpz_clear(v);
    free_mpz_struct(v);
    mpz_clear(prod);
    free_mpz_struct(prod);
}
