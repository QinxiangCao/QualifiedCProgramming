#include "fme_ge_gmp/gmp/gmp_def.h"

void mpz_neg(mpz_t rop, const mpz_t op)
/*@ eq
  With z
  Require rop == op && store_Z(op, z)
  Ensure rop == op && store_Z(op, -z)
*/;

void mpz_add_ui(mpz_t r, const mpz_t a, unsigned long b)
/*@ r_eq_a
  With za b0
  Require r == a && b == b0 && 0 <= b0 && store_Z(a, za)
  Ensure store_Z(a, za + b0)
*/;

void mpz_ui_sub(mpz_t r, unsigned long a, const mpz_t b)
/*@ r_eq_b
  With zb a0
  Require r == b && a == a0 && 0 <= a0 && store_Z(b, zb)
  Ensure store_Z(b, a0 - zb)
*/
{
  mpz_neg(r, b) /*@ where (eq) z = zb */;
  mpz_add_ui(r, r, a) /*@ where (r_eq_a) za = -zb, b0 = a0 */;
}
