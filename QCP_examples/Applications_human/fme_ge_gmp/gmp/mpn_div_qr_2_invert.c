#include "fme_ge_gmp/gmp/gmp_def.h"

unsigned int gmp_clz(unsigned int x)
/*@
  Require 0 < x && x <= UINT_MAX
  Ensure 0 <= __return && __return < 32 &&
          Z::pow(2, 31) <= x * Z::pow(2, __return) &&
          x * Z::pow(2, __return) < Z::pow(2, 32)
*/;

unsigned int mpn_invert_3by2(unsigned int u1, unsigned int u0)
/*@
  Require UINT_MOD / 2 <= u1 && u1 <= UINT_MAX &&
          0 <= u0 && u0 <= UINT_MAX
  Ensure 0 <= __return && __return <= UINT_MAX &&
         (__return + UINT_MOD) * (UINT_MOD * u1 + u0) <=
           Z::pow(UINT_MOD, 3) - 1 &&
         Z::pow(UINT_MOD, 3) - 1 <
           (__return + UINT_MOD + 1) * (UINT_MOD * u1 + u0)
*/;

void mpn_div_qr_2_invert(struct gmp_div_inverse *inv,
                         unsigned int d1, unsigned int d0)
/*@
  Require 0 < d1 && d1 <= UINT_MAX &&
          0 <= d0 && d0 <= UINT_MAX &&
          div_inverse_slot(inv)
  Ensure
          store_div_inverse(inv, 2, d1 * UINT_MOD + d0)
*/
{
  unsigned int shift;

  shift = gmp_clz(d1);
  /*@ Assert
        inv == inv@pre &&
        d1 == d1@pre &&
        d0 == d0@pre &&
        0 < d1 && d1 <= UINT_MAX &&
        0 <= d0 && d0 <= UINT_MAX &&
        0 <= shift && shift < 32 &&
        Z::pow(2, 31) <= d1 * Z::pow(2, shift) &&
        d1 * Z::pow(2, shift) < Z::pow(2, 32) &&
        undef_data_at(&(inv->shift), unsigned int) *
        undef_data_at(&(inv->d1), unsigned int) *
        undef_data_at(&(inv->d0), unsigned int) *
        undef_data_at(&(inv->di), unsigned int)
  */
  inv->shift = shift;
  if (shift > 0) {
    d1 = (d1 << shift) | (d0 >> (32 - shift));
    d0 = d0 << shift;
  }
  /*@ Assert exists nd1 nd0,
        0 <= shift &&
        shift < 32 &&
        Z::pow(2, 31) <= d1@pre * Z::pow(2, shift) &&
        d1@pre * Z::pow(2, shift) < Z::pow(2, 32) &&
        d1 == nd1 &&
        d0 == nd0 &&
        nd1 * UINT_MOD + nd0 ==
          (d1@pre * UINT_MOD + d0@pre) * Z::pow(2, shift) &&
        UINT_MOD / 2 <= nd1 &&
        nd1 <= UINT_MAX &&
        0 <= nd0 &&
        nd0 <= UINT_MAX &&
        inv == inv@pre &&
        inv->shift == shift &&
        undef_data_at(&(inv->d1), unsigned int) *
        undef_data_at(&(inv->d0), unsigned int) *
        undef_data_at(&(inv->di), unsigned int)
  */
  inv->d1 = d1;
  inv->d0 = d0;
  inv->di = mpn_invert_3by2(d1, d0);
}
