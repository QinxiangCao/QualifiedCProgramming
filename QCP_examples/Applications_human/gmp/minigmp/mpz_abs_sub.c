#include "gmp/minigmp/gmp_def.h"

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

unsigned int *mrz_realloc_if(mpz_ptr z,int n)
/*@ preserving
  With
    ptr old cap m
  Require
    cap >= 0 && cap <= INT_MAX && n >= 0 && n <= INT_MAX &&
    Zabs(old) <= cap && same_sign(m, old) &&
    mpd_store_Z_compact(UINT_MOD,ptr, Zabs(m), Zabs(old)) * UIntArray::undef_seg(ptr, Zabs(old), cap) &&
      z -> _mp_size == old &&
      z -> _mp_alloc == cap &&
      z -> _mp_d == ptr
  Ensure
    same_sign(m, old) &&
    mpd_store_Z_compact(UINT_MOD,__return, Zabs(m), Zabs(old)) * UIntArray::undef_seg(__return, Zabs(old), Z::max(n,cap)) &&
    z -> _mp_size == old &&
    z -> _mp_alloc == Z::max(n,cap) &&
    z -> _mp_d == __return
*/;

int mpn_cmp4(unsigned int *ap, int an, unsigned int *bp, int bn)
/*@
  With val1 val2
  Require
    an >= 0 && bn >= 0 && 
    mpd_store_Z_compact(UINT_MOD, ap, val1, an) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, bn)
  Ensure
    (val1 > val2 && __return == 1 ||
    val1 == val2 && __return == 0 ||
    val1 < val2 && __return == -1) &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, an) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, bn)
*/;

unsigned int mpn_sub(unsigned int *rp, unsigned int *ap, int an,
                     unsigned int *bp, int bn)
/*@ non_alias
 With val_a val_b
 Require
   an >= bn && an > 0 && bn >= 0 &&
   mpd_store_Z(UINT_MOD, ap, val_a, an) *
   mpd_store_Z(UINT_MOD, bp, val_b, bn) *
   UIntArray::undef_full(rp, an)
 Ensure
   exists val_r_out,
   (val_r_out - __return * Z::pow(UINT_MOD, an) == val_a - val_b) &&
   mpd_store_Z(UINT_MOD, ap, val_a, an) *
   mpd_store_Z(UINT_MOD, bp, val_b, bn) *
   mpd_store_Z(UINT_MOD, rp, val_r_out, an)
*/
/*@ rp_eq_ap
  With
    val_a val_b
  Require
    rp == ap && an >= bn && an > 0 && bn >= 0 &&
    an <= INT_MAX && bn <= INT_MAX &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn)
  Ensure exists val_r_out,
    val_r_out - __return * Z::pow(UINT_MOD, an) == val_a - val_b &&
    rp == ap &&
    mpd_store_Z(UINT_MOD, ap, val_r_out, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn)
*/
/*@ rp_eq_bp
  With
    val_a val_b
  Require
    rp == bp && an >= bn && an > 0 && bn >= 0 &&
    an <= INT_MAX && bn <= INT_MAX &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn) *
    UIntArray::undef_seg(rp, bn, an)
  Ensure exists val_r_out,
    val_r_out - __return * Z::pow(UINT_MOD, an) == val_a - val_b &&
    rp == bp &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, rp, val_r_out, an)
*/;

int mpn_normalized_size(unsigned int *xp, int n)
/*@ plain
  With val
  Require
    0 <= n && 
    mpd_store_Z(UINT_MOD, xp, val, n) 
  Ensure
    0 <= __return && __return <= n &&
    mpd_store_Z_compact(UINT_MOD, xp, val, __return) * 
    UIntArray::undef_seg(xp, __return, n)
*/;

int mpz_abs_sub(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ non_alias
  With n m l
  Require
    store_Z(a, n) * store_Z(b, m) * store_Z(r, l)
  Ensure
    store_Z(a, n) * store_Z(b, m) *
    store_Z_remain_size(r, Zabs(n) - Zabs(m), __return)
*/
/*@ r_eq_a
  With
    za zb
  Require
    r == a &&
    store_Z(a, za) * store_Z(b, zb)
  Ensure
    store_Z_with_old_size(a, za, Zabs(za) - Zabs(zb), __return) *
    store_Z(b, zb)
*/
{
  int an;
  int bn;
  int cmp;
  unsigned int *rp;

  /*@ Assert
      exists rptr rsize rcap bptr bsize bcap,
      r@pre == a@pre &&
      INT_MIN < rsize && rsize <= INT_MAX &&
      INT_MIN < bsize && bsize <= INT_MAX &&
      0 <= rcap && rcap <= INT_MAX &&
      0 <= bcap && bcap <= INT_MAX &&
      Zabs(rsize) <= rcap && same_sign(za_r_eq_a, rsize) &&
      Zabs(bsize) <= bcap && same_sign(zb_r_eq_a, bsize) &&
      has_permission(&rp) *
      has_permission(&cmp) *
      has_permission(&bn) *
      has_permission(&an) *
      store(&r, r@pre) *
      store(&a, a@pre) *
      store(&b, b@pre) *
      store(&(a@pre->_mp_size), rsize) *
      store(&(a@pre->_mp_alloc), rcap) *
      store(&(a@pre->_mp_d), unsigned int *, rptr) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(za_r_eq_a), Zabs(rsize)) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      store(&(b@pre->_mp_size), bsize) *
      store(&(b@pre->_mp_alloc), bcap) *
      store(&(b@pre->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb_r_eq_a), Zabs(bsize)) *
      UIntArray::undef_seg(bptr, Zabs(bsize), bcap)
  $ r_eq_a */
  /*@ Given rptr rsize rcap bptr bsize bcap $ r_eq_a */
  an = gmp_abs(a->_mp_size);
  bn = gmp_abs(b->_mp_size);
  cmp = mpn_cmp4(a->_mp_d, an, b->_mp_d, bn);
  if (cmp > 0) {
    /*@ Assert
      cmp > 0 && Zabs(za_r_eq_a) > Zabs(zb_r_eq_a) && cmp == 1 &&
      an == Zabs(rsize) && bn == Zabs(bsize) &&
      same_sign(za_r_eq_a, rsize) && same_sign(zb_r_eq_a, bsize) &&
      Zabs(rsize) <= rcap && 0 <= rcap && rcap <= INT_MAX &&
      Zabs(bsize) <= bcap &&
      r == r@pre && r@pre == a@pre && b == b@pre &&
      has_permission(&rp) *
      store(&a, a@pre) *
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap) *
      store(&(r->_mp_d), unsigned int *, rptr) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(za_r_eq_a), Zabs(rsize)) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb_r_eq_a), bn) *
      UIntArray::undef_seg(bptr, bn, bcap)
    $ r_eq_a */
    /*@ 1 <= an && an <= INT_MAX by local $ r_eq_a */
    /*@ 0 <= bn && bn <= INT_MAX by local $ r_eq_a */
    /*@ 0 <= r->_mp_alloc && r->_mp_alloc <= INT_MAX by local $ r_eq_a */
/*@ Assert
      exists rptr rsize rcap,
      cmp > 0 && Zabs(n_non_alias) > Zabs(m_non_alias) && cmp == 1 &&
      bn == Zabs(b@pre->_mp_size) &&
      same_sign(m_non_alias, b@pre->_mp_size) &&
      Zabs(b@pre->_mp_size) <= b@pre->_mp_alloc &&
      an == Zabs(a@pre->_mp_size) &&
      same_sign(n_non_alias, a@pre->_mp_size) &&
      Zabs(a@pre->_mp_size) <= a@pre->_mp_alloc &&
      Zabs(rsize) <= rcap && same_sign(l_non_alias, rsize) && rcap >= 0 &&
      mpd_store_Z_compact(UINT_MOD, a@pre->_mp_d, Zabs(n_non_alias), an) *
      mpd_store_Z_compact(UINT_MOD, b@pre->_mp_d, Zabs(m_non_alias), bn) *
      has_permission(&rp) *
      UIntArray::undef_seg(b@pre->_mp_d, Zabs(b@pre->_mp_size), b@pre->_mp_alloc) *
      UIntArray::undef_seg(a@pre->_mp_d, Zabs(a@pre->_mp_size), a@pre->_mp_alloc) *
      store(&(r->_mp_d), rptr) *
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(l_non_alias), Zabs(rsize)) *
      (b == b@pre) * (a == a@pre) * (r == r@pre)
      $ non_alias
      */
    rp = mrz_realloc_if(r, an);
/*@ Assert
      exists rsize rcap,
      cmp > 0 && Zabs(n_non_alias) > Zabs(m_non_alias) && cmp == 1 &&
      bn == Zabs(b@pre->_mp_size) &&
      same_sign(m_non_alias, b@pre->_mp_size) &&
      Zabs(b@pre->_mp_size) <= b@pre->_mp_alloc &&
      an == Zabs(a@pre->_mp_size) &&
      same_sign(n_non_alias, a@pre->_mp_size) &&
      Zabs(a@pre->_mp_size) <= a@pre->_mp_alloc &&
      same_sign(l_non_alias, rsize) && Zabs(rsize) <= rcap && rcap >= 0 &&
      r->_mp_size == rsize &&
      r->_mp_alloc == Z::max(Z::max(an, 1), rcap) &&
      r->_mp_d == rp &&
      is_compact_Z(UINT_MOD, Zabs(l_non_alias), Zabs(rsize)) &&
      an < Z::max(Z::max(an + 1, 1), rcap) &&
      mpd_store_Z_compact(UINT_MOD, a@pre->_mp_d, Zabs(n_non_alias), an) *
      mpd_store_Z_compact(UINT_MOD, b@pre->_mp_d, Zabs(m_non_alias), bn) *
      UIntArray::undef_seg(b@pre->_mp_d, Zabs(b@pre->_mp_size), b@pre->_mp_alloc) *
      UIntArray::undef_seg(a@pre->_mp_d, Zabs(a@pre->_mp_size), a@pre->_mp_alloc) *
      (b == b@pre) * (a == a@pre) * (r == r@pre) *
      UIntArray::undef_full(rp, an) *
      UIntArray::undef_seg(rp, an, Z::max(Z::max(an, 1), rcap))   
      $ non_alias
      */
    /*@ Assert
      exists rptr_new rcap_new,
      cmp > 0 && Zabs(za_r_eq_a) > Zabs(zb_r_eq_a) && cmp == 1 &&
      an == Zabs(rsize) && bn == Zabs(bsize) &&
      same_sign(za_r_eq_a, rsize) && same_sign(zb_r_eq_a, bsize) &&
      Zabs(rsize) <= rcap_new && 0 <= rcap_new && rcap_new <= INT_MAX &&
      Zabs(bsize) <= bcap &&
      an <= rcap_new &&
      a == r &&
      r == r@pre && r@pre == a@pre && b == b@pre &&
      rp == rptr_new &&
      store(&(a->_mp_size), rsize) *
      store(&(a->_mp_alloc), rcap_new) *
      store(&(a->_mp_d), unsigned int *, rptr_new) *
      mpd_store_Z_compact(UINT_MOD, rptr_new, Zabs(za_r_eq_a), an) *
      UIntArray::undef_seg(rptr_new, an, rcap_new) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb_r_eq_a), bn) *
      UIntArray::undef_seg(bptr, bn, bcap)
    $ r_eq_a */
    mpn_sub(rp, a->_mp_d, an, b->_mp_d, bn)
      /*@ where (non_alias) $ non_alias
          where (rp_eq_ap) val_a = Zabs(za_r_eq_a), val_b = Zabs(zb_r_eq_a) $ r_eq_a */;
    return mpn_normalized_size(rp, an);
  } else if (cmp < 0) {
    /*@ Assert
      cmp < 0 && Zabs(za_r_eq_a) < Zabs(zb_r_eq_a) && cmp == -1 &&
      an == Zabs(rsize) && bn == Zabs(bsize) &&
      same_sign(za_r_eq_a, rsize) && same_sign(zb_r_eq_a, bsize) &&
      Zabs(rsize) <= rcap && 0 <= rcap && rcap <= INT_MAX &&
      Zabs(bsize) <= bcap &&
      r == r@pre && r@pre == a@pre && b == b@pre &&
      has_permission(&rp) *
      store(&a, a@pre) *
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap) *
      store(&(r->_mp_d), unsigned int *, rptr) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(za_r_eq_a), Zabs(rsize)) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb_r_eq_a), bn) *
      UIntArray::undef_seg(bptr, bn, bcap)
    $ r_eq_a */
    /*@ 1 <= bn && bn <= INT_MAX by local $ r_eq_a */
    /*@ 0 <= an && an <= INT_MAX by local $ r_eq_a */
    /*@ 0 <= r->_mp_alloc && r->_mp_alloc <= INT_MAX by local $ r_eq_a */
/*@ Assert
      exists rptr rsize rcap,
      cmp < 0 && cmp <= 0 && Zabs(n_non_alias) < Zabs(m_non_alias) && cmp == -1 &&
      bn == Zabs(b@pre->_mp_size) &&
      same_sign(m_non_alias, b@pre->_mp_size) &&
      Zabs(b@pre->_mp_size) <= b@pre->_mp_alloc &&
      an == Zabs(a@pre->_mp_size) &&
      same_sign(n_non_alias, a@pre->_mp_size) &&
      Zabs(a@pre->_mp_size) <= a@pre->_mp_alloc &&
      Zabs(rsize) <= rcap && same_sign(l_non_alias, rsize) && rcap >= 0 &&
      mpd_store_Z_compact(UINT_MOD, a@pre->_mp_d, Zabs(n_non_alias), an) *
      mpd_store_Z_compact(UINT_MOD, b@pre->_mp_d, Zabs(m_non_alias), bn) *
      has_permission(&rp) *
      UIntArray::undef_seg(b@pre->_mp_d, Zabs(b@pre->_mp_size), b@pre->_mp_alloc) *
      UIntArray::undef_seg(a@pre->_mp_d, Zabs(a@pre->_mp_size), a@pre->_mp_alloc) *
      store(&(r->_mp_d), rptr) *
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(l_non_alias), Zabs(rsize)) *
      (b == b@pre) * (a == a@pre) * (r == r@pre)
      $ non_alias
      */
    rp = mrz_realloc_if(r, bn);
/*@ Assert
      exists rsize rcap,
      cmp < 0 && cmp <= 0 && Zabs(n_non_alias) < Zabs(m_non_alias) && cmp == -1 &&
      bn == Zabs(b@pre->_mp_size) &&
      same_sign(m_non_alias, b@pre->_mp_size) &&
      Zabs(b@pre->_mp_size) <= b@pre->_mp_alloc &&
      an == Zabs(a@pre->_mp_size) &&
      same_sign(n_non_alias, a@pre->_mp_size) &&
      Zabs(a@pre->_mp_size) <= a@pre->_mp_alloc &&
      same_sign(l_non_alias, rsize) && Zabs(rsize) <= rcap && rcap >= 0 &&
      r->_mp_size == rsize &&
      r->_mp_alloc == Z::max(Z::max(bn, 1), rcap) &&
      r->_mp_d == rp &&
      is_compact_Z(UINT_MOD, Zabs(l_non_alias), Zabs(rsize)) &&
      bn < Z::max(Z::max(bn + 1, 1), rcap) &&
      mpd_store_Z_compact(UINT_MOD, a@pre->_mp_d, Zabs(n_non_alias), an) *
      mpd_store_Z_compact(UINT_MOD, b@pre->_mp_d, Zabs(m_non_alias), bn) *
      UIntArray::undef_seg(b@pre->_mp_d, Zabs(b@pre->_mp_size), b@pre->_mp_alloc) *
      UIntArray::undef_seg(a@pre->_mp_d, Zabs(a@pre->_mp_size), a@pre->_mp_alloc) *
      (b == b@pre) * (a == a@pre) * (r == r@pre) *
      UIntArray::undef_full(rp, bn) *
      UIntArray::undef_seg(rp, bn, Z::max(Z::max(bn, 1), rcap))   
      $ non_alias
      */
    /*@ Assert
      exists rptr_new rcap_new,
      cmp < 0 && Zabs(za_r_eq_a) < Zabs(zb_r_eq_a) && cmp == -1 &&
      an == Zabs(rsize) && bn == Zabs(bsize) &&
      same_sign(za_r_eq_a, rsize) && same_sign(zb_r_eq_a, bsize) &&
      Zabs(rsize) <= rcap_new && 0 <= rcap_new && rcap_new <= INT_MAX &&
      Zabs(bsize) <= bcap &&
      bn <= rcap_new &&
      a == r &&
      r == r@pre && r@pre == a@pre && b == b@pre &&
      rp == rptr_new &&
      store(&(a->_mp_size), rsize) *
      store(&(a->_mp_alloc), rcap_new) *
      store(&(a->_mp_d), unsigned int *, rptr_new) *
      mpd_store_Z_compact(UINT_MOD, rptr_new, Zabs(za_r_eq_a), an) *
      UIntArray::undef_seg(rptr_new, an, bn) *
      UIntArray::undef_seg(rptr_new, bn, rcap_new) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb_r_eq_a), bn) *
      UIntArray::undef_seg(bptr, bn, bcap)
    $ r_eq_a */
    mpn_sub(rp, b->_mp_d, bn, a->_mp_d, an)
      /*@ where (non_alias) $ non_alias
          where (rp_eq_bp) val_a = Zabs(zb_r_eq_a), val_b = Zabs(za_r_eq_a) $ r_eq_a */;
    return -mpn_normalized_size(rp, bn);
  } else {
    return 0;
  }
}
