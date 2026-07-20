#include "fme_ge_gmp/ge/ge_def.h"

/*@ include strategies "../gmp/mpz_tdiv_r_read0.strategies" */

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

void mpz_set_ui(mpz_t r, unsigned long x)
/*@
  With old x0
  Require x == x0 && 0 <= x0 && store_Z(r, old)
  Ensure store_Z(r, x0)
*/;

void mpz_sub_ui(mpz_t r, const mpz_t a, unsigned long b)
/*@ r_eq_a
  With za b0
  Require r == a && b == b0 && 0 <= b0 && store_Z(a, za)
  Ensure store_Z(a, za - b0)
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

void mpz_mul(mpz_ptr rop, mpz_srcptr op1, mpz_srcptr op2)
/*@ neq
  With
    old z1 z2
  Require
    store_Z(rop, old) * store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    store_Z(rop, z1 * z2) * store_Z(op1, z1) * store_Z(op2, z2)
*/
/*@ r_eq_op1
  With
    z1 z2
  Require
    rop == op1 &&
    store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    rop == op1 &&
    store_Z(op1, z1 * z2) * store_Z(op2, z2)
*/;

void mpz_tdiv_q_2exp(mpz_ptr r, mpz_srcptr u, unsigned long long cnt)
/*@ eq
  With z
  Require
    r == u &&
    cnt >= 0 &&
    cnt / 32 <= INT_MAX &&
    store_Z(r, z)
  Ensure
    r == u &&
    store_Z(r, Z::quot(z, Z::pow(2, cnt)))
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

int mpz_odd_positive(mpz_srcptr x)
/*@
  With z
  Require
    z > 0 &&
    store_Z(x, z)
  Ensure
    store_Z(x, z) &&
    ((__return == 0 && z % 2 == 0) ||
     (__return == 1 && z % 2 == 1))
*/
{
    unsigned int limb0;

    /*@ Assert
          z > 0 &&
          x == x@pre &&
          undef_data_at(&limb0, unsigned int) *
          store_Z_read0(x, z)
    */
    /*@ Assert
          exists ptr size cap data,
            x == x@pre &&
            z > 0 &&
            Zabs(size) <= cap &&
            same_sign(z, size) &&
            list_to_Z(UINT_MOD, data) == Zabs(z) &&
            last(data, 1) >= 1 &&
            list_within_bound(UINT_MOD, data) &&
            Zlength(data) == Zabs(size) &&
            x->_mp_size == size &&
            x->_mp_alloc == cap &&
            x->_mp_d == ptr &&
            undef_data_at(&limb0, unsigned int) *
            UIntArray::seg(ptr, 0, 1, sublist(0, 1, mpd_read0_data(data))) *
            UIntArray::seg(ptr, 1, Zmax(Zabs(size), 1), sublist(1, Zmax(Zabs(size), 1), mpd_read0_data(data))) *
            UIntArray::undef_seg(ptr, Zmax(Zabs(size), 1), cap)
    */
    limb0 = x->_mp_d[0];
    if (limb0 & 1) {
        return 1;
    }
    return 0;
}

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
*/
{
    mpz_ptr result;
    mpz_ptr base;
    mpz_ptr exp;
    mpz_ptr tmp;
    int s;
    int odd;

    result = malloc_mpz_struct();
    mpz_init(result);
    base = malloc_mpz_struct();
    mpz_init(base);
    exp = malloc_mpz_struct();
    mpz_init(exp);
    tmp = malloc_mpz_struct();
    mpz_init(tmp);

    mpz_set_ui(result, 1);
    mpz_set(tmp, a) /*@ where (neq) old = 0, z = za */;
    mod_norm_gmp(base, tmp, p);
    mpz_set(exp, p) /*@ where (neq) old = 0, z = zp */;
    mpz_sub_ui(exp, exp, 2) /*@ where (r_eq_a) za = zp, b0 = 2 */;
    s = mpz_sgn(exp);

    /*@ Inv Assert
          exists zresult zbase zexp ztmp,
              r != 0 && a != 0 && p != 0 &&
              result != 0 && base != 0 && exp != 0 && tmp != 0 &&
              r == r@pre &&
              a == a@pre &&
              p == p@pre &&
              prime(zp) &&
              0 < za && za < zp &&
              0 <= zresult && zresult < zp &&
              0 <= zbase && zbase < zp &&
              0 <= zexp &&
              same_sign(s, zexp) &&
              mpz_div_qr_ret_ok(s, zexp) &&
              mod_inv_pow_loop(zp, za, zresult, zbase, zexp) &&
              undef_data_at(&odd, int) *
              store_Z(r, old) *
              store_Z(a, za) *
              store_Z(p, zp) *
              store_Z(result, zresult) *
              store_Z(base, zbase) *
              store_Z(exp, zexp) *
              store_Z(tmp, ztmp)
    */
    while (s > 0) {
        odd = mpz_odd_positive(exp);
        if (odd) {
            mpz_mul(tmp, result, base) /*@ where (neq) */;
            mod_norm_gmp(result, tmp, p);
        }
        mpz_set(tmp, base) /*@ where (neq) */;
        mpz_mul(tmp, tmp, base) /*@ where (r_eq_op1) */;
        mod_norm_gmp(base, tmp, p);
        mpz_tdiv_q_2exp(exp, exp, 1) /*@ where (eq) */;
        s = mpz_sgn(exp);
    }

    mpz_set(r, result) /*@ where (neq) */;

    mpz_clear(tmp);
    free_mpz_struct(tmp);
    mpz_clear(exp);
    free_mpz_struct(exp);
    mpz_clear(base);
    free_mpz_struct(base);
    mpz_clear(result);
    free_mpz_struct(result);
}
