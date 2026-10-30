#include "gmp/minigmp/gmp_def.h"

enum mpz_div_round_mode { GMP_DIV_FLOOR, GMP_DIV_CEIL, GMP_DIV_TRUNC };

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

unsigned int *mrz_realloc_if(mpz_ptr z, int n)
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

void mpz_neg(mpz_ptr rop, mpz_srcptr op)
/*@ eq
  With z
  Require rop == op && store_Z(op, z)
  Ensure rop == op && store_Z(op, -z)
*/;

int mpn_zero_p(unsigned int *rp, int n);

void mpz_add_ui(mpz_ptr r, mpz_srcptr a, unsigned long b);

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
*/;

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
*/;

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
