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

void mpn_div_qr_1_invert(struct gmp_div_inverse *inv, unsigned int d)
/*@
  Require 0 < d && d <= UINT_MAX &&
          div_inverse_slot(inv)
  Ensure
          store_div_inverse(inv, 1, d)
*/;

void mpn_div_qr_2_invert(struct gmp_div_inverse *inv,
                         unsigned int d1, unsigned int d0)
/*@
  Require 0 < d1 && d1 <= UINT_MAX &&
          0 <= d0 && d0 <= UINT_MAX &&
          div_inverse_slot(inv)
  Ensure
          store_div_inverse(inv, 2, d1 * UINT_MOD + d0)
*/;

void mpn_div_qr_invert(struct gmp_div_inverse *inv,
                       unsigned int *dp, int dn)
/*@
  With d
  Require dn > 0 && dn <= INT_MAX &&
          mpd_store_Z_compact(UINT_MOD, dp, d, dn) *
          div_inverse_slot(inv)
  Ensure
          mpd_store_Z_compact(UINT_MOD, dp, d, dn) *
          store_div_inverse(inv, dn, d)
*/
{
  /*@ Assert exists l_dp,
      dn == dn@pre && dp == dp@pre && inv == inv@pre &&
      dn > 0 && dn <= INT_MAX &&
      Zlength(l_dp) == dn &&
      list_to_Z(UINT_MOD, l_dp) == d &&
      last(l_dp, 1) >= 1 &&
      list_within_bound(UINT_MOD, l_dp) &&
      UIntArray::full(dp, dn, l_dp) *
      undef_data_at(&(inv->shift), unsigned int) *
      undef_data_at(&(inv->d1), unsigned int) *
      undef_data_at(&(inv->d0), unsigned int) *
      undef_data_at(&(inv->di), unsigned int)
  */
  if (dn == 1) {
    /*@ Assert exists l_dp,
        dn == dn@pre && dp == dp@pre && inv == inv@pre &&
        dn == 1 &&
        dn > 0 && dn <= INT_MAX &&
        Zlength(l_dp) == dn &&
        list_to_Z(UINT_MOD, l_dp) == d &&
        last(l_dp, 1) >= 1 &&
        list_within_bound(UINT_MOD, l_dp) &&
        UIntArray::full(dp, dn, l_dp) *
        div_inverse_slot(inv)
    */
    mpn_div_qr_1_invert(inv, dp[0]);
    /*@ Assert
        dn == dn@pre && dp == dp@pre && inv == inv@pre &&
        dn == 1 &&
        mpd_store_Z_compact(UINT_MOD, dp, d, dn) *
        store_div_inverse(inv, dn, d)
    */
  } else if (dn == 2) {
    /*@ Assert exists l_dp,
        dn == dn@pre && dp == dp@pre && inv == inv@pre &&
        dn == 2 &&
        dn > 0 && dn <= INT_MAX &&
        Zlength(l_dp) == dn &&
        list_to_Z(UINT_MOD, l_dp) == d &&
        last(l_dp, 1) >= 1 &&
        list_within_bound(UINT_MOD, l_dp) &&
        UIntArray::full(dp, dn, l_dp) *
        div_inverse_slot(inv)
    */
    mpn_div_qr_2_invert(inv, dp[1], dp[0]);
    /*@ Assert
        dn == dn@pre && dp == dp@pre && inv == inv@pre &&
        dn == 2 &&
        mpd_store_Z_compact(UINT_MOD, dp, d, dn) *
        store_div_inverse(inv, dn, d)
    */
  } else {
    unsigned int shift;
    unsigned int d1;
    unsigned int d0;

    d1 = dp[dn - 1];
    d0 = dp[dn - 2];
    shift = gmp_clz(d1);
    inv->shift = shift;
    if (shift > 0) {
      d1 = (d1 << shift) | (d0 >> (32 - shift));
      d0 = (d0 << shift) | (dp[dn - 3] >> (32 - shift));
    }
    inv->d1 = d1;
    inv->d0 = d0;
    inv->di = mpn_invert_3by2(d1, d0);
    /*@ Assert
        dn == dn@pre && dp == dp@pre && inv == inv@pre &&
        dn > 2 &&
        mpd_store_Z_compact(UINT_MOD, dp, d, dn) *
        store_div_inverse(inv, dn, d) *
        has_permission(&shift) *
        has_permission(&d1) *
        has_permission(&d0)
    */
  }
}
