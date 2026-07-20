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

int mpz_sgn(const mpz_t u)
/*@
  With n
  Require store_Z(u, n)
  Ensure
    store_Z(u, n) &&
    (n > 0 && __return == 1 || n == 0 && __return == 0 ||
     n < 0 && __return == -1)
*/;

void mod_inv_gmp(mpz_ptr r, mpz_srcptr a, mpz_srcptr p)
/*@ low_level_spec
    With old za zp
    Require r != 0 && a != 0 && p != 0 &&
            prime(zp) &&
            0 < za && za < zp &&
            store_Z(r, old) * store_Z(a, za) * store_Z(p, zp)
    Ensure exists inv,
            mod_inverse_spec(zp, za, inv) &&
            store_Z(r, inv) * store_Z(a, za) * store_Z(p, zp)
*/;

void row_swap_mod_gmp(int n, mpz_srcptr p, mpz_ptr aug, int r1, int r2)
/*@ low_level_spec
    With M l zp
    Require aug != 0 &&
            0 <= n && n <= 256 &&
            0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
            0 <= r1 && r1 < n &&
            0 <= r2 && r2 < n &&
            rep_matrix(l, n, n + 1, M) &&
            store_Z(p, zp) *
            mpz_array(aug, n * (n + 1), l)
    Ensure exists l2,
           rep_matrix(l2, n, n + 1, matrix_row_swap(M, r1, r2)) &&
           store_Z(p, zp) *
           mpz_array(aug, n * (n + 1), l2)
*/;

void row_scale_mod_gmp(int n, mpz_srcptr p, mpz_ptr aug, int row, mpz_srcptr inv)
/*@ low_level_spec
    With M l zp zinv
    Require aug != 0 && p != 0 && inv != 0 &&
            0 <= n && n <= 256 &&
            zp > 0 &&
            0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
            0 <= row && row < n &&
            0 <= zinv && zinv < zp &&
            rep_matrix(l, n, n + 1, M) &&
            mat_mod(zp, n, n + 1, M) &&
            store_Z(p, zp) *
            store_Z(inv, zinv) *
            mpz_array(aug, n * (n + 1), l)
    Ensure exists l2,
           rep_matrix(l2, n, n + 1, matrix_row_scale_mod(zp, M, row, zinv)) &&
           mat_mod(zp, n, n + 1, matrix_row_scale_mod(zp, M, row, zinv)) &&
           store_Z(p, zp) *
           store_Z(inv, zinv) *
           mpz_array(aug, n * (n + 1), l2)
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
*/
{
    int cols = n + 1;
    int k = 0;

    /*@ Inv Assert
          aug != 0 && x != 0 && p != 0 && aug != x &&
          aug == aug@pre && x == x@pre && p == p@pre &&
          n == n@pre &&
          cols == n + 1 &&
          cols == n@pre + 1 &&
          0 <= n && n <= 256 &&
          2 <= zp &&
          prime(zp) &&
          0 <= n * cols && n * cols <= INT_MAX &&
          0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
          Zlength(lx) == n &&
          rep_matrix(l, n, cols, M0) &&
          mat_mod(zp, n, cols, M0) &&
          0 <= k && k <= n &&
          exists M lcur,
            rep_matrix(lcur, n, cols, M) &&
            gauss_inv(zp, n, k, M0, M) &&
            store_Z(p, zp) *
            mpz_array(aug, n * cols, lcur) *
            mpz_array(x, n, lx)
    */
    while (k < n) {
        /*@ Given M lcur */
        int pivot = k;
        int ps = 0;
        /*@ Inv Assert
              aug != 0 && x != 0 && p != 0 && aug != x &&
              aug == aug@pre && x == x@pre && p == p@pre &&
              n == n@pre &&
              cols == n + 1 &&
              cols == n@pre + 1 &&
              0 <= n && n <= 256 &&
              2 <= zp &&
              prime(zp) &&
              0 <= n * cols && n * cols <= INT_MAX &&
              0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
              Zlength(lx) == n &&
              rep_matrix(l, n, cols, M0) &&
              mat_mod(zp, n, cols, M0) &&
              0 <= k && k < n &&
              k <= pivot && pivot <= n &&
              (pivot >= n || (0 <= pivot * cols + k && pivot * cols + k < n * cols)) &&
              INT_MIN <= pivot * cols && pivot * cols <= INT_MAX &&
              INT_MIN <= pivot * cols + k && pivot * cols + k <= INT_MAX &&
              (ps == 0 || ps == 1 || ps == -1) &&
              (ps != 0 => pivot < n && Znth(pivot * cols + k, lcur, 0) != 0) &&
              rep_matrix(lcur, n, cols, M) &&
              gauss_inv(zp, n, k, M0, M) &&
              pivot_search_zero_prefix(n, k, pivot, M) &&
              store_Z(p, zp) *
              mpz_array(aug, n * cols, lcur) *
              mpz_array(x, n, lx)
        */
        while (pivot < n && ps == 0) {
            int pidx = pivot * cols + k;
            ps = mpz_sgn(aug + pidx);
            if (ps == 0) {
                pivot = pivot + 1;
            }
        }

        if (pivot == n) {
            return 0;
        }

        if (pivot != k) {
            /*@ Assert
                  aug != 0 && x != 0 && p != 0 && aug != x &&
                  aug == aug@pre && x == x@pre && p == p@pre &&
                  n == n@pre &&
                  cols == n + 1 &&
                  0 <= n && n <= 256 &&
                  2 <= zp &&
                  prime(zp) &&
                  0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
                  Zlength(lx) == n &&
                  rep_matrix(l, n, cols, M0) &&
                  mat_mod(zp, n, cols, M0) &&
                  0 <= k && k < n &&
                  k <= pivot &&
                  0 <= pivot && pivot < n &&
                  Znth(pivot * cols + k, lcur, 0) != 0 &&
                  rep_matrix(lcur, n, n + 1, M) &&
                  gauss_inv(zp, n, k, M0, M) &&
                  pivot_search_zero_prefix(n, k, pivot, M) &&
                  store_Z(p, zp) *
                  mpz_array(aug, n * (n + 1), lcur) *
                  mpz_array(x, n, lx) *
                  data_at(&ps, ps)
            */
            row_swap_mod_gmp(n, p, aug, k, pivot);
        }

        /*@ Assert
              aug != 0 && x != 0 && p != 0 && aug != x &&
              aug == aug@pre && x == x@pre && p == p@pre &&
              n == n@pre &&
              cols == n + 1 &&
              cols == n@pre + 1 &&
              0 <= n && n <= 256 &&
              2 <= zp &&
              prime(zp) &&
              0 <= n * cols && n * cols <= INT_MAX &&
              0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
              Zlength(lx) == n &&
              rep_matrix(l, n, cols, M0) &&
              mat_mod(zp, n, cols, M0) &&
              0 <= k && k < n &&
              k <= pivot && pivot < n &&
              0 <= k * cols + k && k * cols + k < n * cols &&
              INT_MIN <= k * cols && k * cols <= INT_MAX &&
              INT_MIN <= k * cols + k && k * cols + k <= INT_MAX &&
              exists M1 l1,
                rep_matrix(l1, n, cols, M1) &&
                mat_mod(zp, n, cols, M1) &&
                gauss_inv(zp, n, k, M0, M1) &&
                0 < Znth(k * cols + k, l1, 0) &&
                Znth(k * cols + k, l1, 0) < zp &&
                store_Z(p, zp) *
                mpz_array(aug, n * cols, l1) *
                mpz_array(x, n, lx) *
                data_at(&ps, ps)
        */
        /*@ Given M1 l1 */
        mpz_ptr pv;
        mpz_ptr inv;
        mpz_ptr factor;

        pv = malloc_mpz_struct();
        mpz_init(pv);
        inv = malloc_mpz_struct();
        mpz_init(inv);
        factor = malloc_mpz_struct();
        mpz_init(factor);

        mpz_set(pv, aug + (k * cols + k)) /*@ where (neq) */;
        mod_inv_gmp(inv, pv, p);
        /*@ Assert exists zinv,
              aug != 0 && x != 0 && p != 0 && aug != x &&
              pv != 0 && inv != 0 && factor != 0 &&
              aug == aug@pre && x == x@pre && p == p@pre &&
              n == n@pre &&
              cols == n + 1 &&
              0 <= n && n <= 256 &&
              2 <= zp &&
              prime(zp) &&
              0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
              Zlength(lx) == n &&
              rep_matrix(l, n, cols, M0) &&
              mat_mod(zp, n, cols, M0) &&
              0 <= k && k < n &&
              k <= pivot && pivot < n &&
              0 <= zinv && zinv < zp &&
              mod_inverse_spec(zp, Znth(k * cols + k, l1, 0), zinv) &&
              rep_matrix(l1, n, n + 1, M1) &&
              mat_mod(zp, n, n + 1, M1) &&
              gauss_inv(zp, n, k, M0, M1) &&
              store_Z(p, zp) *
              store_Z(pv, Znth(k * cols + k, l1, 0)) *
              store_Z(inv, zinv) *
              store_Z(factor, 0) *
              mpz_array(aug, n * (n + 1), l1) *
              mpz_array(x, n, lx) *
              data_at(&ps, ps)
        */
        row_scale_mod_gmp(n, p, aug, k, inv);

        /*@ Assert exists zinv M2 l2,
              aug != 0 && x != 0 && p != 0 && aug != x &&
              pv != 0 && inv != 0 && factor != 0 &&
              aug == aug@pre && x == x@pre && p == p@pre &&
              n == n@pre &&
              cols == n + 1 &&
              cols == n@pre + 1 &&
              0 <= n && n <= 256 &&
              2 <= zp &&
              prime(zp) &&
              0 <= n * cols && n * cols <= INT_MAX &&
              0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
              Zlength(lx) == n &&
              rep_matrix(l, n, cols, M0) &&
              mat_mod(zp, n, cols, M0) &&
              0 <= k && k < n &&
              k <= pivot && pivot < n &&
              0 <= zinv && zinv < zp &&
              rep_matrix(l2, n, cols, M2) &&
              mat_mod(zp, n, cols, M2) &&
              gauss_inv(zp, n, k, M0, M2) &&
              pivot_column_prefix_ready(zp, n, k, 0, M2) &&
              store_Z(p, zp) *
              store_Z(pv, Znth(k * cols + k, l1, 0)) *
              store_Z(inv, zinv) *
              store_Z(factor, 0) *
              mpz_array(aug, n * cols, l2) *
              mpz_array(x, n, lx) *
              data_at(&ps, ps)
        */
        /*@ Given zinv M2 l2 */

        int i = 0;
        /*@ Inv Assert
              exists Mcur lcur2 zfactor,
                aug != 0 && x != 0 && p != 0 && aug != x &&
                pv != 0 && inv != 0 && factor != 0 &&
                aug == aug@pre && x == x@pre && p == p@pre &&
                n == n@pre &&
                cols == n + 1 &&
                cols == n@pre + 1 &&
                0 <= n && n <= 256 &&
                2 <= zp &&
                prime(zp) &&
                0 <= n * cols && n * cols <= INT_MAX &&
                0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
                Zlength(lx) == n &&
                rep_matrix(l, n, cols, M0) &&
                mat_mod(zp, n, cols, M0) &&
                0 <= k && k < n &&
                k <= pivot && pivot < n &&
                0 <= i && i <= n &&
                (i >= n || (0 <= i * cols + k && i * cols + k < n * cols)) &&
                INT_MIN <= i * cols && i * cols <= INT_MAX &&
                INT_MIN <= i * cols + k && i * cols + k <= INT_MAX &&
                rep_matrix(lcur2, n, cols, Mcur) &&
                mat_mod(zp, n, cols, Mcur) &&
                gauss_inv(zp, n, k, M0, Mcur) &&
                pivot_column_prefix_ready(zp, n, k, i, Mcur) &&
                store_Z(p, zp) *
                store_Z(pv, Znth(k * cols + k, l1, 0)) *
                store_Z(inv, zinv) *
                store_Z(factor, zfactor) *
                mpz_array(aug, n * cols, lcur2) *
                mpz_array(x, n, lx) *
                data_at(&ps, ps)
        */
        while (i < n) {
            /*@ Given Mcur lcur2 zfactor */
            if (i != k) {
                int fs;
                mpz_set(factor, aug + (i * cols + k)) /*@ where (neq) */;
                /*@ Assert
                      aug != 0 && x != 0 && p != 0 && aug != x &&
                      pv != 0 && inv != 0 && factor != 0 &&
                      aug == aug@pre && x == x@pre && p == p@pre &&
                      n == n@pre &&
                      cols == n + 1 &&
                      0 <= n && n <= 256 &&
                      2 <= zp &&
                      prime(zp) &&
                      0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
                      Zlength(lx) == n &&
                      rep_matrix(l, n, cols, M0) &&
                      mat_mod(zp, n, cols, M0) &&
                      0 <= k && k < n &&
                      k <= pivot && pivot < n &&
                      0 <= i && i < n &&
                      i != k &&
                      0 <= Znth(i * cols + k, lcur2, 0) &&
                      Znth(i * cols + k, lcur2, 0) < zp &&
                      rep_matrix(lcur2, n, n + 1, Mcur) &&
                      mat_mod(zp, n, n + 1, Mcur) &&
                      gauss_inv(zp, n, k, M0, Mcur) &&
                      pivot_column_prefix_ready(zp, n, k, i, Mcur) &&
                      store_Z(p, zp) *
                      store_Z(pv, Znth(k * cols + k, l1, 0)) *
                      store_Z(inv, zinv) *
                      store_Z(factor, Znth(i * cols + k, lcur2, 0)) *
                      mpz_array(aug, n * (n + 1), lcur2) *
                      mpz_array(x, n, lx) *
                      data_at(&ps, ps) *
                      undef_data_at(&fs, int)
                */
                fs = mpz_sgn(factor);
                if (fs != 0) {
                    row_elim_mod_gmp(n, p, aug, k, i, factor)
                        /*@ where (low_level_spec) M = Mcur, l = lcur2 */
                        ;
                }
            }
            i = i + 1;
            /*@ Assert
                  aug != 0 && x != 0 && p != 0 && aug != x &&
                  pv != 0 && inv != 0 && factor != 0 &&
                  aug == aug@pre && x == x@pre && p == p@pre &&
                  n == n@pre &&
                  cols == n + 1 &&
                  cols == n@pre + 1 &&
                  0 <= n && n <= 256 &&
                  2 <= zp &&
                  prime(zp) &&
                  0 <= n * cols && n * cols <= INT_MAX &&
                  0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
                  Zlength(lx) == n &&
                  rep_matrix(l, n, cols, M0) &&
                  mat_mod(zp, n, cols, M0) &&
                  0 <= k && k < n &&
                  k <= pivot && pivot < n &&
                  0 <= i && i <= n &&
                  (i >= n || (0 <= i * cols + k && i * cols + k < n * cols)) &&
                  INT_MIN <= i * cols && i * cols <= INT_MAX &&
                  INT_MIN <= i * cols + k && i * cols + k <= INT_MAX &&
                  exists Mnext lnext zfactor2,
                    rep_matrix(lnext, n, cols, Mnext) &&
                    mat_mod(zp, n, cols, Mnext) &&
                    gauss_inv(zp, n, k, M0, Mnext) &&
                    pivot_column_prefix_ready(zp, n, k, i, Mnext) &&
                    store_Z(p, zp) *
                    store_Z(pv, Znth(k * cols + k, l1, 0)) *
                    store_Z(inv, zinv) *
                    store_Z(factor, zfactor2) *
                    mpz_array(aug, n * cols, lnext) *
                    mpz_array(x, n, lx) *
                    data_at(&ps, ps)
            */
        }

        /*@ Assert
              aug != 0 && x != 0 && p != 0 && aug != x &&
              pv != 0 && inv != 0 && factor != 0 &&
              aug == aug@pre && x == x@pre && p == p@pre &&
              n == n@pre &&
              cols == n + 1 &&
              cols == n@pre + 1 &&
              0 <= n && n <= 256 &&
              2 <= zp &&
              prime(zp) &&
              0 <= n * cols && n * cols <= INT_MAX &&
              0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
              Zlength(lx) == n &&
              rep_matrix(l, n, cols, M0) &&
              mat_mod(zp, n, cols, M0) &&
              0 <= k && k < n &&
              k <= pivot && pivot < n &&
              exists Mdone ldone zfactor3,
                rep_matrix(ldone, n, cols, Mdone) &&
                mat_mod(zp, n, cols, Mdone) &&
                gauss_inv(zp, n, k, M0, Mdone) &&
                pivot_column_ready(zp, n, k, Mdone) &&
                rref_prefix_mod(zp, n, k + 1, Mdone) &&
                store_Z(p, zp) *
                store_Z(pv, Znth(k * cols + k, l1, 0)) *
                store_Z(inv, zinv) *
                store_Z(factor, zfactor3) *
                mpz_array(aug, n * cols, ldone) *
                mpz_array(x, n, lx) *
                data_at(&ps, ps) *
                data_at(&i, i)
        */
        /*@ Given Mdone ldone zfactor3 */

        mpz_clear(factor);
        free_mpz_struct(factor);
        mpz_clear(inv);
        free_mpz_struct(inv);
        mpz_clear(pv);
        free_mpz_struct(pv);

        k = k + 1;
        /*@ Assert
              aug != 0 && x != 0 && p != 0 && aug != x &&
              aug == aug@pre && x == x@pre && p == p@pre &&
              pv != 0 && inv != 0 && factor != 0 &&
              n == n@pre &&
              cols == n + 1 &&
              cols == n@pre + 1 &&
              0 <= n && n <= 256 &&
              2 <= zp &&
              prime(zp) &&
              0 <= n * cols && n * cols <= INT_MAX &&
              0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
              Zlength(lx) == n &&
              rep_matrix(l, n, cols, M0) &&
              mat_mod(zp, n, cols, M0) &&
              0 <= k && k <= n &&
              0 <= pivot && pivot < n &&
              rep_matrix(ldone, n, cols, Mdone) &&
              gauss_inv(zp, n, k, M0, Mdone) &&
              store_Z(p, zp) *
              mpz_array(aug, n * cols, ldone) *
              mpz_array(x, n, lx) *
              data_at(&ps, ps) *
              data_at(&i, i)
        */
    }

    /*@ Assert
          aug != 0 && x != 0 && p != 0 && aug != x &&
          aug == aug@pre && x == x@pre && p == p@pre &&
          n == n@pre &&
          cols == n + 1 &&
          cols == n@pre + 1 &&
          0 <= n && n <= 256 &&
          2 <= zp &&
          prime(zp) &&
          0 <= n * cols && n * cols <= INT_MAX &&
          0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
          Zlength(lx) == n &&
          rep_matrix(l, n, cols, M0) &&
          mat_mod(zp, n, cols, M0) &&
          exists Mfin lfin,
            rep_matrix(lfin, n, cols, Mfin) &&
            gauss_inv(zp, n, n, M0, Mfin) &&
            gauss_finished_matrix(zp, n, Mfin) &&
            store_Z(p, zp) *
            mpz_array(aug, n * cols, lfin) *
            mpz_array(x, n, lx) *
            data_at(&k, k)
    */
    /*@ Given Mfin lfin */
    int i = 0;
    /*@ Inv Assert
          aug != 0 && x != 0 && p != 0 && aug != x &&
          aug == aug@pre && x == x@pre && p == p@pre &&
          n == n@pre &&
          cols == n + 1 &&
          cols == n@pre + 1 &&
          0 <= n && n <= 256 &&
          2 <= zp &&
          prime(zp) &&
          0 <= n * cols && n * cols <= INT_MAX &&
          0 <= n * (n + 1) && n * (n + 1) <= INT_MAX &&
          rep_matrix(l, n, cols, M0) &&
          mat_mod(zp, n, cols, M0) &&
          rep_matrix(lfin, n, cols, Mfin) &&
          gauss_inv(zp, n, n, M0, Mfin) &&
          gauss_finished_matrix(zp, n, Mfin) &&
          0 <= i && i <= n &&
          (i >= n || (0 <= i * cols + n && i * cols + n < n * cols)) &&
          INT_MIN <= i * cols && i * cols <= INT_MAX &&
          INT_MIN <= i * cols + n && i * cols + n <= INT_MAX &&
          exists lxcur,
            rhs_copy_prefix(lxcur, n, i, Mfin) &&
            store_Z(p, zp) *
            mpz_array(aug, n * cols, lfin) *
            mpz_array(x, n, lxcur) *
            data_at(&k, k)
    */
    while (i < n) {
        mpz_set(x + i, aug + (i * cols + n)) /*@ where (neq) */;
        i = i + 1;
    }

    return 1;
}
