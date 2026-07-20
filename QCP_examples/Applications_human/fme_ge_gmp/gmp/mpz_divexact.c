#include "fme_ge_gmp/gmp/gmp_def.h"

enum mpz_div_round_mode { GMP_DIV_FLOOR, GMP_DIV_CEIL, GMP_DIV_TRUNC };

/* Allows q or r to be zero. Returns 1 iff remainder is non-zero. */
static int
mpz_div_qr(mpz_ptr q, mpz_ptr r,
           mpz_srcptr n, mpz_srcptr d, enum mpz_div_round_mode mode)
/*@ nonalias
  With q0 r0 n0 d0 mode0 old_q old_r zn zd
  Require
    q == q0 &&
    r == r0 &&
    n == n0 &&
    d == d0 &&
    mode == mode0 &&
    zd != 0 &&
    mode0 == GMP_DIV_TRUNC &&
    store_Z(n0, zn) * store_Z(d0, zd) *
    optional_store_Z(q0, old_q) *
    optional_store_Z(r0, old_r)
  Ensure exists qv rv,
    mpz_div_qr_math(mode0, zn, zd, qv, rv) &&
    0 <= __return && __return <= 1 &&
    mpz_div_qr_ret_ok(__return, rv) &&
    store_Z(n0, zn) * store_Z(d0, zd) *
    optional_store_Z(q0, qv) *
    optional_store_Z(r0, rv)
*/
;

void
mpz_divexact(mpz_ptr q, mpz_srcptr num, mpz_srcptr den)
/*@
  With
    old zn zd
  Require
    q != 0 &&
    zd != 0 &&
    zn == (zn / zd) * zd &&
    store_Z(q, old) * store_Z(num, zn) * store_Z(den, zd)
  Ensure
    store_Z(q, zn / zd) * store_Z(num, zn) * store_Z(den, zd)
*/
{
  /*@ Assert
    q == q@pre &&
    num == num@pre &&
    den == den@pre &&
    q != 0 &&
    zd != 0 &&
    zn == (zn / zd) * zd &&
    store_Z(num, zn) * store_Z(den, zd) *
    optional_store_Z(q, old) *
    optional_store_Z(0, 0)
  */
  mpz_div_qr(q, 0, num, den, GMP_DIV_TRUNC)
    /*@ where (nonalias) q0 = q, r0 = 0, n0 = num, d0 = den,
               mode0 = GMP_DIV_TRUNC, old_q = old, old_r = 0,
               zn = zn, zd = zd */;
  /*@ Assert exists qv rv,
    q == q@pre &&
    num == num@pre &&
    den == den@pre &&
    q != 0 &&
    zd != 0 &&
    zn == (zn / zd) * zd &&
    qv == zn / zd &&
    rv == 0 &&
    mpz_div_qr_math(GMP_DIV_TRUNC, zn, zd, qv, rv) &&
    store_Z(num, zn) * store_Z(den, zd) *
    store_Z(q, qv) *
    optional_store_Z(0, rv)
  */
}
