#include "fme_ge_gmp/gmp/gmp_def.h"

unsigned int
mpn_add_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
/*@ rp_eq_ap
  With val_a val_b
  Require
    rp == ap && n >= 0 &&
    mpd_store_Z(UINT_MOD, ap, val_a, n) *
    mpd_store_Z(UINT_MOD, bp, val_b, n)
  Ensure exists val_r_out,
    (val_r_out + __return * Z::pow(UINT_MOD, n) == val_a + val_b) &&
    rp == ap &&
    mpd_store_Z(UINT_MOD, rp, val_r_out, n) *
    mpd_store_Z(UINT_MOD, bp, val_b, n)
*/
/*@ rp_eq_bp
  With val_a val_b
  Require
    rp == bp && n >= 0 &&
    mpd_store_Z(UINT_MOD, ap, val_a, n) *
    mpd_store_Z(UINT_MOD, bp, val_b, n)
  Ensure exists val_r_out,
    (val_r_out + __return * Z::pow(UINT_MOD, n) == val_a + val_b) &&
    rp == bp &&
    mpd_store_Z(UINT_MOD, ap, val_a, n) *
    mpd_store_Z(UINT_MOD, rp, val_r_out, n)
*/;

unsigned int
mpn_add_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
/*@ rp_eq_ap
  With val b0
  Require
    rp == ap && n > 0 && b == b0 && 0 <= b0 && b0 <= UINT_MAX &&
    mpd_store_Z(UINT_MOD, ap, val, n)
  Ensure exists val',
    (val' + __return * Z::pow(UINT_MOD, n) == val + b0) &&
    rp == ap &&
    mpd_store_Z(UINT_MOD, rp, val', n)
*/
/*@ non_alias
  With val b0
  Require
    rp != ap && n > 0 && b == b0 && 0 <= b0 && b0 <= UINT_MAX &&
    mpd_store_Z(UINT_MOD, ap, val, n) *
    UIntArray::undef_full(rp, n)
  Ensure exists val',
    (val' + __return * Z::pow(UINT_MOD, n) == val + b0) &&
    mpd_store_Z(UINT_MOD, ap, val, n) *
    mpd_store_Z(UINT_MOD, rp, val', n)
*/;

unsigned int
mpn_add(unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
/*@ rp_eq_ap
  With
    val_a val_b
  Require
    rp == ap && an >= bn && an >= 0 && bn >= 0 &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn)
  Ensure exists val_r_out,
    val_r_out + __return * Z::pow(UINT_MOD, an) == val_a + val_b &&
    rp == ap &&
    mpd_store_Z(UINT_MOD, ap, val_r_out, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn)
*/
/*@ rp_eq_bp
  With
    val_a val_b
  Require
    rp == bp && an >= bn && an >= 0 && bn >= 0 &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn) *
    UIntArray::undef_seg(rp, bn, an)
  Ensure exists val_r_out,
    val_r_out + __return * Z::pow(UINT_MOD, an) == val_a + val_b &&
    rp == bp &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, rp, val_r_out, an)
*/
/*@ rp_eq_ap */
/*@ rp_eq_bp */
{
  unsigned int cy;
  /*@
    mpd_store_Z(UINT_MOD, ap, val_a_rp_eq_ap, an) && an >= bn && bn >= 0
    $ rp_eq_ap
    which implies
      exists val_a_low val_a_high,
        val_a_rp_eq_ap == val_a_low + val_a_high * Z::pow(UINT_MOD, bn) &&
        mpd_store_Z(UINT_MOD, ap, val_a_low, bn) *
        mpd_store_Z(UINT_MOD, ap + bn * sizeof(unsigned int), val_a_high, an - bn)
  */
  /*@
    mpd_store_Z(UINT_MOD, ap, val_a_rp_eq_bp, an) && an >= bn && bn >= 0
    $ rp_eq_bp
    which implies
      exists val_a_low val_a_high,
        val_a_rp_eq_bp == val_a_low + val_a_high * Z::pow(UINT_MOD, bn) &&
        mpd_store_Z(UINT_MOD, ap, val_a_low, bn) *
        mpd_store_Z(UINT_MOD, ap + bn * sizeof(unsigned int), val_a_high, an - bn)
  */
  /*@ Given val_a_low val_a_high */
  cy = mpn_add_n(rp, ap, bp, bn)
    /*@ where (rp_eq_ap) val_a = val_a_low, val_b = val_b_rp_eq_ap $ rp_eq_ap
        where (rp_eq_bp) val_a = val_a_low, val_b = val_b_rp_eq_bp $ rp_eq_bp */;
  /*@ 0 <= cy && cy <= UINT_MAX by local */
  /*@ Assert
    exists val_r_low,
      rp == bp &&
      rp == rp@pre && ap == ap@pre && bp == bp@pre &&
      an == an@pre && bn == bn@pre &&
      an >= bn && an >= 0 && bn >= 0 &&
      0 <= cy && cy <= UINT_MAX &&
      val_r_low + cy * Z::pow(UINT_MOD, bn) == val_a_low + val_b_rp_eq_bp &&
      val_a_rp_eq_bp == val_a_low + val_a_high * Z::pow(UINT_MOD, bn) &&
      mpd_store_Z(UINT_MOD, ap, val_a_low, bn) *
      mpd_store_Z(UINT_MOD, rp, val_r_low, bn) *
      mpd_store_Z(UINT_MOD, ap + bn * sizeof(unsigned int), val_a_high, an - bn) *
      UIntArray::undef_full(rp + bn * sizeof(unsigned int), an - bn)
      $ rp_eq_bp
  */
  /*@ Assert
    exists val_r_low,
      rp == ap &&
      rp == rp@pre && ap == ap@pre && bp == bp@pre &&
      an == an@pre && bn == bn@pre &&
      an >= bn && an >= 0 && bn >= 0 &&
      0 <= cy && cy <= UINT_MAX &&
      val_r_low + cy * Z::pow(UINT_MOD, bn) == val_a_low + val_b_rp_eq_ap &&
      val_a_rp_eq_ap == val_a_low + val_a_high * Z::pow(UINT_MOD, bn) &&
      mpd_store_Z(UINT_MOD, rp, val_r_low, bn) *
      mpd_store_Z(UINT_MOD, bp, val_b_rp_eq_ap, bn) *
      mpd_store_Z(UINT_MOD, ap + bn * sizeof(unsigned int), val_a_high, an - bn)
      $ rp_eq_ap
  */
  if (an > bn) {
    /*@ Assert
      exists val_r_low,
        rp == bp &&
        rp == rp@pre && ap == ap@pre && bp == bp@pre &&
        an == an@pre && bn == bn@pre &&
        an > bn && an >= bn && bn >= 0 &&
        an - bn > 0 &&
        0 <= cy && cy <= UINT_MAX &&
        val_r_low + cy * Z::pow(UINT_MOD, bn) == val_a_low + val_b_rp_eq_bp &&
        val_a_rp_eq_bp == val_a_low + val_a_high * Z::pow(UINT_MOD, bn) &&
        mpd_store_Z(UINT_MOD, ap, val_a_low, bn) *
        mpd_store_Z(UINT_MOD, rp, val_r_low, bn) *
        mpd_store_Z(UINT_MOD, ap + bn * sizeof(unsigned int), val_a_high, an - bn) *
        UIntArray::undef_full(rp + bn * sizeof(unsigned int), an - bn)
        $ rp_eq_bp
    */
    /*@ Assert
      exists val_r_low,
        rp == ap &&
        rp == rp@pre && ap == ap@pre && bp == bp@pre &&
        an == an@pre && bn == bn@pre &&
        an > bn && an >= bn && bn >= 0 &&
        an - bn > 0 &&
        0 <= cy && cy <= UINT_MAX &&
        val_r_low + cy * Z::pow(UINT_MOD, bn) == val_a_low + val_b_rp_eq_ap &&
        val_a_rp_eq_ap == val_a_low + val_a_high * Z::pow(UINT_MOD, bn) &&
        mpd_store_Z(UINT_MOD, rp, val_r_low, bn) *
        mpd_store_Z(UINT_MOD, bp, val_b_rp_eq_ap, bn) *
        mpd_store_Z(UINT_MOD, ap + bn * sizeof(unsigned int), val_a_high, an - bn)
        $ rp_eq_ap
    */
    /*@ Branch name
        rp_eq_bp: rp == bp;
        rp_eq_ap: rp == ap
    */
    cy = mpn_add_1(rp + bn, ap + bn, an - bn, cy)
      /*@ where (rp_eq_ap) val = val_a_high, b0 = cy $ rp_eq_ap
          where (non_alias) val = val_a_high, b0 = cy $ rp_eq_bp */;
    /*@ 0 <= cy && cy <= UINT_MAX by local */
  }
  /*@ Assert
    exists val_r_out,
      rp == bp &&
      rp == rp@pre && ap == ap@pre && bp == bp@pre &&
      an == an@pre && bn == bn@pre &&
      0 <= cy && cy <= UINT_MAX &&
      val_r_out + cy * Z::pow(UINT_MOD, an) == val_a_rp_eq_bp + val_b_rp_eq_bp &&
      mpd_store_Z(UINT_MOD, ap, val_a_rp_eq_bp, an) *
      mpd_store_Z(UINT_MOD, rp, val_r_out, an)
      $ rp_eq_bp
  */
  /*@ Assert
    exists val_r_out,
      rp == ap &&
      rp == rp@pre && ap == ap@pre && bp == bp@pre &&
      an == an@pre && bn == bn@pre &&
      0 <= cy && cy <= UINT_MAX &&
      val_r_out + cy * Z::pow(UINT_MOD, an) == val_a_rp_eq_ap + val_b_rp_eq_ap &&
      mpd_store_Z(UINT_MOD, ap, val_r_out, an) *
      mpd_store_Z(UINT_MOD, bp, val_b_rp_eq_ap, bn)
      $ rp_eq_ap
  */
  return cy;
}
