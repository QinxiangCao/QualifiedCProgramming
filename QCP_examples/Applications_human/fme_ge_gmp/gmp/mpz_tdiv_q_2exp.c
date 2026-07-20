#include "fme_ge_gmp/gmp/gmp_def.h"

enum mpz_div_round_mode { GMP_DIV_FLOOR, GMP_DIV_CEIL, GMP_DIV_TRUNC };

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

unsigned int *mrz_realloc_if(mpz_t z, int n)
/*@
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

void mpz_neg(mpz_t rop, const mpz_t op)
/*@ eq
  With z
  Require rop == op && store_Z(op, z)
  Ensure rop == op && store_Z(op, -z)
*/;

int mpn_zero_p(unsigned int *rp, int n);

void mpz_add_ui(mpz_t r, const mpz_t a, unsigned long b);

void
mpn_copyi(unsigned int *d, unsigned int *s, int n)
/*@ shifted
  With l off
  Require
    n >= 0 && n + off <= INT_MAX && off >= 0 &&
    s == d + off * sizeof(unsigned int) &&
    Zlength(l) == n + off &&
    list_within_bound(UINT_MOD, l) &&
    UIntArray::full(d, n + off, l)
  Ensure
    UIntArray::seg(d, 0, n, sublist(off, off + n, l)) *
    UIntArray::seg(d, n, n + off, sublist(n, n + off, l))
*/
{
  int i;
  /*@ Destruct with
        off_zero: off == 0;
        off_pos: off > 0
  */
  /*@ Assert
        d == d@pre &&
        s == s@pre &&
        n == n@pre &&
        off == 0 &&
        n >= 0 &&
        n + off <= INT_MAX &&
        s == d + off * sizeof(unsigned int) &&
        Zlength(l) == n + off &&
        list_within_bound(UINT_MOD, l) &&
        has_permission(&i) *
        UIntArray::seg(d, 0, 0, nil) *
        UIntArray::seg(d, 0, n, sublist(0, n, l)) $ off_zero
  */
  /*@ Assert
        d == d@pre &&
        s == s@pre &&
        n == n@pre &&
        off > 0 &&
        n >= 0 &&
        n + off <= INT_MAX &&
        s == d + off * sizeof(unsigned int) &&
        Zlength(l) == n + off &&
        list_within_bound(UINT_MOD, l) &&
        has_permission(&i) *
        UIntArray::seg(d, 0, 0, nil) *
        UIntArray::seg(d, 0, n + off, sublist(0, n + off, l)) $ off_pos
  */
  /*@ Branch name
        off_zero: off == 0;
        off_pos: off > 0
  */
  /*@ Inv
        off_zero:
          d == d@pre &&
          s == s@pre &&
          n == n@pre &&
          off == 0 &&
          n >= 0 &&
          s == d &&
          0 <= i &&
          i <= n@pre &&
          Zlength(l) == n@pre &&
          list_within_bound(UINT_MOD, l) &&
          UIntArray::seg(d@pre, 0, i, sublist(0, i, l)) *
          UIntArray::seg(d@pre, i, n@pre, sublist(i, n@pre, l));
        off_pos:
          d == d@pre &&
          s == s@pre &&
          n == n@pre &&
          off > 0 &&
          n >= 0 &&
          n + off <= INT_MAX &&
          s == d + off * sizeof(unsigned int) &&
          0 <= i &&
          i <= n@pre &&
          Zlength(l) == n@pre + off &&
          list_within_bound(UINT_MOD, l) &&
          UIntArray::seg(d@pre, 0, i, sublist(off, off + i, l)) *
          UIntArray::seg(d@pre, i, n@pre + off, sublist(i, n@pre + off, l))
  */
  for (i = 0; i < n; i++) {
    /*@
      d == d@pre &&
      s == d &&
      0 <= i &&
      i < n@pre &&
      Zlength(l) == n@pre &&
      UIntArray::seg(d@pre, i, n@pre, sublist(i, n@pre, l))
      $ off_zero
      which implies
      d == d@pre &&
      s == d &&
      UIntArray::seg(d@pre, i, i + 1, sublist(i, i + 1, l)) *
      UIntArray::seg(d@pre, i + 1, n@pre, sublist(i + 1, n@pre, l))
    */
    /*@
      d == d@pre &&
      s == s@pre &&
      s == d + off * sizeof(unsigned int) &&
      off > 0 &&
      0 <= i &&
      i < n@pre &&
      Zlength(l) == n@pre + off &&
      UIntArray::seg(d@pre, i, n@pre + off, sublist(i, n@pre + off, l))
      $ off_pos
      which implies
      d == d@pre &&
      s == s@pre &&
      s == d + off * sizeof(unsigned int) &&
      UIntArray::seg(d@pre, i, i + 1, sublist(i, i + 1, l)) *
      UIntArray::seg(d@pre, i + 1, off + i, sublist(i + 1, off + i, l)) *
      UIntArray::seg(s@pre, i, i + 1, sublist(off + i, off + i + 1, l)) *
      UIntArray::seg(d@pre, off + i + 1, n@pre + off, sublist(off + i + 1, n@pre + off, l))
    */
    d[i] = s[i];
    /*@ off_zero ==> off_zero */
    /*@ off_pos ==> off_pos */
  }
}

unsigned int
mpn_rshift(unsigned int *rp, unsigned int *up, int n, unsigned int cnt)
/*@ shifted
  With l_up off
  Require
    n > 0 && n + off <= INT_MAX && off >= 0 &&
    1 <= cnt && cnt < 32 &&
    up == rp + off * sizeof(unsigned int) &&
    Zlength(l_up) == n + off &&
    list_within_bound(UINT_MOD, l_up) &&
    UIntArray::full(rp, n + off, l_up)
  Ensure exists l_out,
    Zlength(l_out) == n &&
    list_within_bound(UINT_MOD, l_out) &&
    __return == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, 32 - cnt), 32) &&
    list_to_Z(UINT_MOD, sublist(off, off + n, l_up)) ==
      list_to_Z(UINT_MOD, l_out) * Z::pow(2, cnt) +
      __return / Z::pow(2, 32 - cnt) &&
    UIntArray::seg(rp, 0, n, l_out) *
    UIntArray::seg(rp, n, n + off, sublist(n, n + off, l_up))
*/
{
  unsigned int high_limb;
  unsigned int low_limb;
  unsigned int tnc;
  unsigned int retval;

  tnc = 32 - cnt;
  /*@
    rp == rp@pre &&
    up == up@pre &&
    n == n@pre &&
    cnt == cnt@pre &&
    off >= 0 &&
    n > 0 &&
    n + off <= INT_MAX &&
    up == rp + off * sizeof(unsigned int) &&
    Zlength(l_up) == n + off &&
    UIntArray::full(rp, n + off, l_up)
    which implies
    rp == rp@pre &&
    up == up@pre &&
    n == n@pre &&
    cnt == cnt@pre &&
    up == rp + off * sizeof(unsigned int) &&
    UIntArray::seg(rp, 0, off, sublist(0, off, l_up)) *
    UIntArray::seg(up, 0, 1, sublist(off, off + 1, l_up)) *
    UIntArray::seg(rp, off + 1, n + off, sublist(off + 1, n + off, l_up))
  */
  high_limb = up[0];
  up++;
  retval = high_limb << tnc;
  low_limb = high_limb >> cnt;
  --n;

  /*@ Assert exists i l_done,
        rp == rp@pre &&
        up == up@pre + (i + 1) * sizeof(unsigned int) &&
        n == n@pre - i - 1 &&
        cnt == cnt@pre &&
        off >= 0 &&
        n@pre > 0 &&
        n@pre + off <= INT_MAX &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        tnc == 32 - cnt@pre &&
        up@pre == rp@pre + off * sizeof(unsigned int) &&
        i == 0 &&
        0 <= i &&
        i < n@pre &&
        Zlength(l_up) == n@pre + off &&
        l_done == nil &&
        Zlength(l_done) == i &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        high_limb == Znth(off + i, l_up, 0) &&
        low_limb == Znth(off + i, l_up, 0) / Z::pow(2, cnt@pre) &&
        retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(off, off + i + 1, l_up)) ==
          (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
            Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        UIntArray::seg(rp@pre, 0, i, l_done) *
        UIntArray::seg(rp@pre, i, n@pre + off, sublist(i, n@pre + off, l_up)) */

  /*@ Inv Assert
        exists i l_done,
          rp == rp@pre + i * sizeof(unsigned int) &&
          up == up@pre + (i + 1) * sizeof(unsigned int) &&
          n == n@pre - i - 1 &&
          cnt == cnt@pre &&
          off >= 0 &&
          n@pre > 0 &&
          n@pre + off <= INT_MAX &&
          1 <= cnt@pre &&
          cnt@pre < 32 &&
          tnc == 32 - cnt@pre &&
          up@pre == rp@pre + off * sizeof(unsigned int) &&
          0 <= i &&
          i < n@pre &&
          Zlength(l_up) == n@pre + off &&
          Zlength(l_done) == i &&
          list_within_bound(UINT_MOD, l_up) &&
          list_within_bound(UINT_MOD, l_done) &&
          high_limb == Znth(off + i, l_up, 0) &&
          low_limb == Znth(off + i, l_up, 0) / Z::pow(2, cnt@pre) &&
          retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
          list_to_Z(UINT_MOD, sublist(off, off + i + 1, l_up)) ==
            (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
              Z::pow(2, cnt@pre) +
            retval / Z::pow(2, tnc) &&
          UIntArray::seg(rp@pre, 0, i, l_done) *
          UIntArray::seg(rp@pre, i, n@pre + off, sublist(i, n@pre + off, l_up))
  */
  while (n != 0)
    {
      /*@ Assert exists i l_done,
        rp == rp@pre + i * sizeof(unsigned int) &&
        up == up@pre + (i + 1) * sizeof(unsigned int) &&
        up@pre == rp@pre + off * sizeof(unsigned int) &&
        n == n@pre - i - 1 &&
        n != 0 &&
        off >= 0 &&
        n@pre > 0 &&
        n@pre + off <= INT_MAX &&
        cnt == cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        tnc == 32 - cnt@pre &&
        0 <= i &&
        i + 1 < n@pre &&
        Zlength(l_up) == n@pre + off &&
        Zlength(l_done) == i &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        high_limb == Znth(off + i, l_up, 0) &&
        low_limb == Znth(off + i, l_up, 0) / Z::pow(2, cnt@pre) &&
        retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(off, off + i + 1, l_up)) ==
          (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
            Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        UIntArray::seg(rp@pre, 0, i, l_done) *
        UIntArray::seg(rp, 0, 1, sublist(i, i + 1, l_up)) *
        UIntArray::seg(rp@pre, i + 1, off + i + 1, sublist(i + 1, off + i + 1, l_up)) *
        UIntArray::seg(up, 0, 1, sublist(off + i + 1, off + i + 2, l_up)) *
        UIntArray::seg(rp@pre, off + i + 2, n@pre + off, sublist(off + i + 2, n@pre + off, l_up))
      */
      high_limb = up[0];
      up++;
      rp[0] = low_limb | (high_limb << tnc);
      rp++;
      low_limb = high_limb >> cnt;
      --n;
      /*@ Assert exists i l_done,
        rp == rp@pre + i * sizeof(unsigned int) &&
        up == up@pre + (i + 1) * sizeof(unsigned int) &&
        n == n@pre - i - 1 &&
        cnt == cnt@pre &&
        off >= 0 &&
        n@pre > 0 &&
        n@pre + off <= INT_MAX &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        tnc == 32 - cnt@pre &&
        up@pre == rp@pre + off * sizeof(unsigned int) &&
        0 <= i &&
        i < n@pre &&
        Zlength(l_up) == n@pre + off &&
        Zlength(l_done) == i &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        high_limb == Znth(off + i, l_up, 0) &&
        low_limb == Znth(off + i, l_up, 0) / Z::pow(2, cnt@pre) &&
        retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(off, off + i + 1, l_up)) ==
          (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
            Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        UIntArray::seg(rp@pre, 0, i, l_done) *
        UIntArray::seg(rp@pre, i, n@pre + off, sublist(i, n@pre + off, l_up)) */
    }
  /*@ Assert exists i l_done,
      rp == rp@pre + i * sizeof(unsigned int) &&
      up == up@pre + (i + 1) * sizeof(unsigned int) &&
      n == 0 &&
      n == n@pre - i - 1 &&
      cnt == cnt@pre &&
      off >= 0 &&
      n@pre > 0 &&
      n@pre + off <= INT_MAX &&
      1 <= cnt@pre &&
      cnt@pre < 32 &&
      tnc == 32 - cnt@pre &&
      up@pre == rp@pre + off * sizeof(unsigned int) &&
      0 <= i &&
      i < n@pre &&
      Zlength(l_up) == n@pre + off &&
      Zlength(l_done) == i &&
      list_within_bound(UINT_MOD, l_up) &&
      list_within_bound(UINT_MOD, l_done) &&
      high_limb == Znth(off + i, l_up, 0) &&
      low_limb == Znth(off + i, l_up, 0) / Z::pow(2, cnt@pre) &&
      retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
      list_to_Z(UINT_MOD, sublist(off, off + i + 1, l_up)) ==
        (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
          Z::pow(2, cnt@pre) +
        retval / Z::pow(2, tnc) &&
      UIntArray::seg(rp@pre, 0, i, l_done) *
      UIntArray::seg(rp, 0, 1, sublist(i, i + 1, l_up)) *
      UIntArray::seg(rp@pre, i + 1, n@pre + off, sublist(i + 1, n@pre + off, l_up))
  */
  rp[0] = low_limb;
  /*@ Assert exists l_out,
        rp == rp@pre + (n@pre - 1) * sizeof(unsigned int) &&
        up == up@pre + n@pre * sizeof(unsigned int) &&
        n == 0 &&
        cnt == cnt@pre &&
        off >= 0 &&
        n@pre > 0 &&
        n@pre + off <= INT_MAX &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        tnc == 32 - cnt@pre &&
        up@pre == rp@pre + off * sizeof(unsigned int) &&
        Zlength(l_up) == n@pre + off &&
        Zlength(l_out) == n@pre &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_out) &&
        retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(off, off + n@pre, l_up)) ==
          list_to_Z(UINT_MOD, l_out) * Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        has_permission(&high_limb) *
        has_permission(&low_limb) *
        UIntArray::seg(rp@pre, 0, n@pre, l_out) *
        UIntArray::seg(rp@pre, n@pre, n@pre + off, sublist(n@pre, n@pre + off, l_up)) */

  return retval;
}

static void
mpz_div_q_2exp(mpz_ptr q, mpz_srcptr u, unsigned long long bit_index,
               enum mpz_div_round_mode mode)
/*@ eq_trunc
  With z
  Require
	    q == u &&
	    mode == GMP_DIV_TRUNC &&
	    bit_index >= 0 &&
	    bit_index / 32 <= INT_MAX &&
	    store_Z(q, z)
  Ensure
    q == u &&
    store_Z(q, Z::quot(z, Z::pow(2, bit_index)))
*/
{
  int un;
  int qn;
  int limb_cnt;
  unsigned int *qp;
  int adjust;

  /*@ Assert
        exists ptr size cap,
          q == q@pre &&
          u == u@pre &&
          q == u &&
          mode == GMP_DIV_TRUNC &&
          mode == mode@pre &&
          bit_index == bit_index@pre &&
          bit_index >= 0 &&
          bit_index / 32 <= INT_MAX &&
          Zabs(size) <= cap &&
          cap >= 0 &&
          cap <= INT_MAX &&
          same_sign(z, size) &&
          has_permission(&un) *
          has_permission(&qn) *
          has_permission(&limb_cnt) *
          has_permission(&qp) *
          has_permission(&adjust) *
          store(&(u->_mp_size), size) *
          store(&(u->_mp_alloc), cap) *
          store(&(u->_mp_d), ptr) *
          mpd_store_Z_compact(UINT_MOD, ptr, Zabs(z), Zabs(size)) *
          UIntArray::undef_seg(ptr, Zabs(size), cap)
  */
  un = u->_mp_size;
  if (un == 0)
    {
      q->_mp_size = 0;
      return;
    }
  limb_cnt = bit_index / 32;
  qn = gmp_abs(un) - limb_cnt;
  bit_index %= 32;

  if (mode == ((un > 0) ? GMP_DIV_CEIL : GMP_DIV_FLOOR))
    adjust = (qn <= 0
              || !mpn_zero_p(u->_mp_d, limb_cnt)
              || (u->_mp_d[limb_cnt]
                  & (((unsigned int) 1 << bit_index) - 1)));
  else
    adjust = 0;

  if (qn <= 0)
    qn = 0;
  else
    {
      qp = mrz_realloc_if(q, qn);
	      /*@ Assert exists l cap,
	            q == q@pre &&
	            u == u@pre &&
	            q == u &&
            mode == mode@pre &&
            mode == GMP_DIV_TRUNC &&
            bit_index@pre >= 0 &&
            bit_index@pre / 32 <= INT_MAX &&
            bit_index == bit_index@pre % 32 &&
            bit_index >= 0 &&
            bit_index < 32 &&
            un != 0 &&
            Zabs(un) <= cap &&
            cap >= 0 &&
            cap <= INT_MAX &&
            same_sign(z, un) &&
            adjust == 0 &&
            limb_cnt == bit_index@pre / 32 &&
            qn == Zabs(un) - limb_cnt &&
            qn > 0 &&
            qn + limb_cnt == Zabs(un) &&
            Zlength(l) == qn + limb_cnt &&
            list_to_Z(UINT_MOD, l) == Zabs(z) &&
            list_within_bound(UINT_MOD, l) &&
            last(l, 1) >= 1 &&
            u->_mp_size == un &&
            u->_mp_alloc == Z::max(qn, cap) &&
            u->_mp_d == qp &&
            UIntArray::full(qp, qn + limb_cnt, l) *
            UIntArray::undef_seg(qp, qn + limb_cnt, Z::max(qn, cap)) */
      /*@ Given l cap */

      if (bit_index != 0)
        {
          mpn_rshift(qp, u->_mp_d + limb_cnt, qn, bit_index)
            /*@ where (shifted) l_up = l, off = limb_cnt */;
          qn -= qp[qn - 1] == 0;
        }
      else
        {
          mpn_copyi(qp, u->_mp_d + limb_cnt, qn)
            /*@ where (shifted) l = l, off = limb_cnt */;
        }
    }

  q->_mp_size = qn;

  if (adjust)
    mpz_add_ui(q, q, 1);
  if (un < 0)
    {
      /*@ Assert
            q == q@pre &&
            u == u@pre &&
            q == u &&
            mode == mode@pre &&
            bit_index@pre >= 0 &&
            un < 0 &&
            same_sign(z, un) &&
            store_Z(q, Z::quot(Zabs(z), Z::pow(2, bit_index@pre))) *
	            has_permission(&bit_index) *
	            has_permission(&qn) *
            has_permission(&limb_cnt) *
            has_permission(&qp) *
            has_permission(&adjust) */
      mpz_neg(q, q) /*@ where (eq) z = Z::quot(Zabs(z), Z::pow(2, bit_index@pre)) */;
    }
}

void
mpz_tdiv_q_2exp(mpz_ptr r, mpz_srcptr u, unsigned long long cnt)
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
*/
{
  mpz_div_q_2exp(r, u, cnt, GMP_DIV_TRUNC) /*@ where (eq_trunc) z = z */;
}
