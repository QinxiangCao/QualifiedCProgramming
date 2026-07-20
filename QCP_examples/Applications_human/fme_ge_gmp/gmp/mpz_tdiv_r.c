#include "fme_ge_gmp/gmp/gmp_def.h"

enum mpz_div_round_mode { GMP_DIV_FLOOR, GMP_DIV_CEIL, GMP_DIV_TRUNC };

/* Allows q or r to be zero. Returns 1 iff remainder is non-zero. */
static int
mpz_div_qr(mpz_ptr q, mpz_ptr r,
           mpz_srcptr n, mpz_srcptr d, enum mpz_div_round_mode mode)
/*@ r_eq_n
  With q0 r0 n0 d0 mode0 old_q zn zd
  Require
    q == q0 &&
    r == r0 &&
    n == n0 &&
    d == d0 &&
    mode == mode0 &&
    r0 == n0 &&
    n0 != 0 &&
    zd != 0 &&
    mode0 == GMP_DIV_TRUNC &&
    store_Z(n0, zn) * store_Z(d0, zd) *
    optional_store_Z(q0, old_q)
  Ensure exists qv rv,
    r0 == n0 &&
    mpz_div_qr_math(mode0, zn, zd, qv, rv) &&
    0 <= __return && __return <= 1 &&
    mpz_div_qr_ret_ok(__return, rv) &&
    store_Z(n0, rv) * store_Z(d0, zd) *
    optional_store_Z(q0, qv)
*/
;

void
mpz_tdiv_r(mpz_ptr r, mpz_srcptr n, mpz_srcptr d)
/*@ r_eq_n
  With zn zd
  Require
    r == n &&
    n != 0 &&
    zd != 0 &&
    store_Z(n, zn) * store_Z(d, zd)
  Ensure exists qv rv,
    r == n &&
    zd != 0 &&
    zn == qv * zd + rv &&
    Zabs(rv) < Zabs(zd) &&
    (rv == 0 || same_sign(rv, zn)) &&
    store_Z(n, rv) * store_Z(d, zd)
*/
{
  /*@ Assert
    r == r@pre &&
    n == n@pre &&
    d == d@pre &&
    r == n &&
    n != 0 &&
    zd != 0 &&
    store_Z(n, zn) * store_Z(d, zd) *
    optional_store_Z(0, 0)
  */
  mpz_div_qr(0, r, n, d, GMP_DIV_TRUNC)
    /*@ where (r_eq_n) q0 = 0, r0 = r, n0 = n, d0 = d,
               mode0 = GMP_DIV_TRUNC, old_q = 0,
               zn = zn, zd = zd */;
  /*@ Assert exists qv rv,
    r == r@pre &&
    n == n@pre &&
    d == d@pre &&
    r == n &&
    zd != 0 &&
    zn == qv * zd + rv &&
    Zabs(rv) < Zabs(zd) &&
    (rv == 0 || same_sign(rv, zn)) &&
    store_Z(n, rv) * store_Z(d, zd) *
    optional_store_Z(0, qv)
  */
}
