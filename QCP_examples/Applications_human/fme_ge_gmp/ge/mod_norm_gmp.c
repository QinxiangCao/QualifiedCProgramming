#include "fme_ge_gmp/ge/ge_def.h"

void mpz_set(mpz_t rop, const mpz_t op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure  store_Z(rop, z) * store_Z(op, z)
*/;

void mpz_tdiv_r(mpz_ptr r, mpz_srcptr n, mpz_srcptr d)
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

void mpz_add(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ r_eq_a
  With za zb
  Require
    r == a && store_Z(a, za) * store_Z(b, zb)
  Ensure
    store_Z(a, za + zb) * store_Z(b, zb)
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
*/
{
  int s;

  mpz_set(r, x) /*@ where (neq) old = old, z = zx */;
  mpz_tdiv_r(r, r, p) /*@ where (r_eq_n) zn = zx, zd = zp */;

  /*@ Assert exists qv rv,
        r == r@pre &&
        x == x@pre &&
        p == p@pre &&
        zp > 0 &&
        zx == qv * zp + rv &&
        Zabs(rv) < Zabs(zp) &&
        (rv == 0 || same_sign(rv, zx)) &&
        undef_data_at(&s, int) *
        store_Z(r, rv) * store_Z(x, zx) * store_Z(p, zp)
  */
  /*@ Given qv rv */
  s = mpz_sgn(r) /*@ where n = rv */;

  if (s < 0) {
    /*@ Assert
          s == -1 &&
          r == r@pre &&
          x == x@pre &&
          p == p@pre &&
          zp > 0 &&
          rv < 0 &&
          zx == qv * zp + rv &&
          Zabs(rv) < Zabs(zp) &&
          (rv == 0 || same_sign(rv, zx)) &&
          store_Z(r, rv) * store_Z(x, zx) * store_Z(p, zp)
    */
    mpz_add(r, r, p) /*@ where (r_eq_a) za = rv, zb = zp */;
    /*@ Assert
          s == -1 &&
          r == r@pre &&
          x == x@pre &&
          p == p@pre &&
          zp > 0 &&
          mod_norm_spec(zp, zx, rv + zp) &&
          store_Z(r, rv + zp) * store_Z(x, zx) * store_Z(p, zp)
    */
  } else {
    /*@ Assert
          s >= 0 &&
          r == r@pre &&
          x == x@pre &&
          p == p@pre &&
          zp > 0 &&
          0 <= rv &&
          zx == qv * zp + rv &&
          Zabs(rv) < Zabs(zp) &&
          (rv == 0 || same_sign(rv, zx)) &&
          mod_norm_spec(zp, zx, rv) &&
          store_Z(r, rv) * store_Z(x, zx) * store_Z(p, zp)
    */
  }
}
