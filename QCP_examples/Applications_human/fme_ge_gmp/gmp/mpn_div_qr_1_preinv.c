#include "fme_ge_gmp/gmp/gmp_def.h"

/*@ Extern Coq (optional_q_undef : Z -> Z -> Assertion)
               (optional_q_full : Z -> Z -> list Z -> Assertion) */

static unsigned int *
gmp_alloc_limbs (int size)
/*@
  Require
    size >= 0
  Ensure
    UIntArray::undef_full(__return, size)
*/;

static void
gmp_free_limbs (unsigned int *old, int size)
/*@
  With
    n len
  Require
    mpd_store_Z_compact(UINT_MOD,old, n, len) *
    UIntArray::undef_seg(old, len, size)
  Ensure
    emp
*/;

unsigned int mpn_lshift(unsigned int *rp, unsigned int *up,
                        int n, unsigned int cnt)
/*@ nonalias
  With l_up
  Require rp != up &&
          n > 0 && n <= INT_MAX &&
          1 <= cnt && cnt < 32 &&
          Zlength(l_up) == n &&
          list_within_bound(UINT_MOD, l_up) &&
          UIntArray::undef_full(rp, n) *
          UIntArray::full(up, n, l_up)
  Ensure exists l_out,
          Zlength(l_out) == n &&
          list_within_bound(UINT_MOD, l_out) &&
          list_to_Z(UINT_MOD, l_out) + __return * Z::pow(UINT_MOD, n) ==
            list_to_Z(UINT_MOD, l_up) * Z::pow(2, cnt) &&
          UIntArray::full(rp, n, l_out) *
          UIntArray::full(up, n, l_up)
*/
/*@ inplace
  With l_up
  Require rp == up &&
          n > 0 && n <= INT_MAX &&
          1 <= cnt && cnt < 32 &&
          Zlength(l_up) == n &&
          list_within_bound(UINT_MOD, l_up) &&
          UIntArray::full(up, n, l_up)
  Ensure exists l_out,
          Zlength(l_out) == n &&
          list_within_bound(UINT_MOD, l_out) &&
          list_to_Z(UINT_MOD, l_out) + __return * Z::pow(UINT_MOD, n) ==
            list_to_Z(UINT_MOD, l_up) * Z::pow(2, cnt) &&
          UIntArray::full(rp, n, l_out)
*/;

void gmp_udiv_qrnnd_preinv(unsigned int *q, unsigned int *r,
                           unsigned int nh, unsigned int nl,
                           unsigned int d, unsigned int di)
/*@
  Require 0 <= nh && nh < d &&
          0 <= nl && nl <= UINT_MAX &&
          UINT_MOD / 2 <= d && d <= UINT_MAX &&
          0 <= di && di <= UINT_MAX &&
          (di + UINT_MOD) * (UINT_MOD * d) <= Z::pow(UINT_MOD, 3) - 1 &&
          Z::pow(UINT_MOD, 3) - 1 <
            (di + UINT_MOD + 1) * (UINT_MOD * d) &&
          has_uint_permission(q) *
          has_uint_permission(r)
  Ensure exists qv rv,
          0 <= qv && qv <= UINT_MAX &&
          0 <= rv && rv < d &&
          nh * UINT_MOD + nl == qv * d + rv &&
          store_uint(q, qv) *
          store_uint(r, rv)
*/;

unsigned int mpn_div_qr_1_preinv(unsigned int *qp, unsigned int *np,
                                 int nn, struct gmp_div_inverse *inv)
/*@ bare
  With qp0 np0 nn0 inv0 l_np d_orig
  Require qp0 == qp && np0 == np && nn0 == nn && inv0 == inv &&
          nn > 0 && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          list_within_bound(UINT_MOD, l_np) &&
          ((qp == 0 && emp) ||
           (qp != 0 && qp != np && UIntArray::undef_full(qp, nn))) *
          UIntArray::full(np, nn, l_np) *
          store_div_inverse(inv, 1, d_orig)
  Ensure exists l_q qv,
          Zlength(l_q) == nn0 &&
          list_within_bound(UINT_MOD, l_q) &&
          list_to_Z(UINT_MOD, l_q) == qv &&
          list_to_Z(UINT_MOD, l_np) == qv * d_orig + __return &&
          0 <= __return && __return < d_orig &&
          ((qp0 == 0 && emp) ||
           (qp0 != 0 && UIntArray::full(qp0, nn0, l_q))) *
          UIntArray::full(np0, nn0, l_np) *
          store_div_inverse(inv0, 1, d_orig)
*/;

unsigned int mpn_div_qr_1_preinv(unsigned int *qp, unsigned int *np,
                                 int nn, struct gmp_div_inverse *inv)
/*@ optional <= bare
  With qp0 np0 nn0 inv0 l_np d_orig
  Require qp0 == qp && np0 == np && nn0 == nn && inv0 == inv &&
          nn > 0 && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          list_within_bound(UINT_MOD, l_np) &&
          optional_q_undef(qp, nn) *
          UIntArray::full(np, nn, l_np) *
          store_div_inverse(inv, 1, d_orig)
  Ensure exists l_q qv,
          Zlength(l_q) == nn0 &&
          list_within_bound(UINT_MOD, l_q) &&
          list_to_Z(UINT_MOD, l_q) == qv &&
          list_to_Z(UINT_MOD, l_np) == qv * d_orig + __return &&
          0 <= __return && __return < d_orig &&
          optional_q_full(qp0, nn0, l_q) *
          UIntArray::full(np0, nn0, l_np) *
          store_div_inverse(inv0, 1, d_orig)
*/;

unsigned int mpn_div_qr_1_preinv(unsigned int *qp, unsigned int *np,
                                 int nn, struct gmp_div_inverse *inv)
/*@ bare */
{
  unsigned int d;
  unsigned int di;
  unsigned int r;
  unsigned int *np_orig;
  unsigned int *tp;
  int tn;

  /*@ Assert exists shift_orig d1_orig d0_orig di_orig,
        qp0 == qp && np0 == np && nn0 == nn && inv0 == inv &&
        nn > 0 && nn <= INT_MAX &&
        0 < d_orig &&
        0 <= shift_orig && shift_orig < 32 &&
        d1_orig == d_orig * Z::pow(2, shift_orig) &&
        d_orig * Z::pow(2, shift_orig) < UINT_MOD &&
        UINT_MOD / 2 <= d1_orig && d1_orig <= UINT_MAX &&
        0 <= d0_orig && d0_orig <= UINT_MAX &&
        0 <= di_orig && di_orig <= UINT_MAX &&
        (di_orig + UINT_MOD) * (UINT_MOD * d1_orig) <=
          Z::pow(UINT_MOD, 3) - 1 &&
        Z::pow(UINT_MOD, 3) - 1 <
          (di_orig + UINT_MOD + 1) * (UINT_MOD * d1_orig) &&
        Zlength(l_np) == nn &&
        list_within_bound(UINT_MOD, l_np) &&
        ((qp == 0 && emp) ||
         (qp != 0 && qp != np && UIntArray::undef_full(qp, nn))) *
        UIntArray::full(np, nn, l_np) *
        store(&(inv->shift), shift_orig) *
        store(&(inv->d1), d1_orig) *
        undef_data_at(&(inv->d0), unsigned int) *
        store(&(inv->di), di_orig) *
        has_uint_permission(&d) *
        has_uint_permission(&di) *
        has_uint_permission(&r) *
        undef_data_at(&np_orig, unsigned int *) *
        undef_data_at(&tp, unsigned int *) *
        undef_data_at(&tn, int)
  */
  np_orig = np;
  tp = (void *)0;
  tn = 0;

  if (inv->shift > 0)
    {
      tp = qp;
      if (tp == (void *)0)
        {
          tn = nn;
          tp = gmp_alloc_limbs(tn);
        }
	      /*@ Assert exists shift_orig d1_orig d0_orig di_orig,
	            qp0 == qp && np0 == np && nn0 == nn && inv0 == inv &&
	            np_orig == np0 &&
	            nn0 > 0 && nn0 <= INT_MAX &&
	            1 <= shift_orig && shift_orig < 32 &&
            0 < d_orig &&
            d1_orig == d_orig * Z::pow(2, shift_orig) &&
            d_orig * Z::pow(2, shift_orig) < UINT_MOD &&
            UINT_MOD / 2 <= d1_orig && d1_orig <= UINT_MAX &&
            0 <= d0_orig && d0_orig <= UINT_MAX &&
            0 <= di_orig && di_orig <= UINT_MAX &&
            (di_orig + UINT_MOD) * (UINT_MOD * d1_orig) <=
              Z::pow(UINT_MOD, 3) - 1 &&
            Z::pow(UINT_MOD, 3) - 1 <
              (di_orig + UINT_MOD + 1) * (UINT_MOD * d1_orig) &&
            Zlength(l_np) == nn &&
            list_within_bound(UINT_MOD, l_np) &&
            ((qp0 == 0 && tp != np && tn == nn) ||
             (qp0 != 0 && tp == qp0 && tp != np && tn == 0)) &&
            UIntArray::undef_full(tp, nn) *
            UIntArray::full(np, nn, l_np) *
            store(&(inv->shift), shift_orig) *
            store(&(inv->d1), d1_orig) *
            undef_data_at(&(inv->d0), unsigned int) *
            store(&(inv->di), di_orig) *
            has_uint_permission(&d) *
            has_uint_permission(&di) *
            has_uint_permission(&r)
      */
      r = mpn_lshift(tp, np, nn, inv->shift)
          /*@ where (nonalias) l_up = l_np */;
      np = tp;
    }
  else
    r = 0;

  d = inv->d1;
  di = inv->di;

  nn = nn - 1;
  /*@ Inv Assert exists shift_orig d1_orig d0_orig di_orig l_cur l_done qv_done carry,
        d == d1_orig &&
        di == di_orig &&
        qp0 == qp && np0 == np_orig && inv0 == inv &&
        0 < d_orig &&
        0 <= shift_orig && shift_orig < 32 &&
        d1_orig == d_orig * Z::pow(2, shift_orig) &&
        d_orig * Z::pow(2, shift_orig) < UINT_MOD &&
        UINT_MOD / 2 <= d1_orig && d1_orig <= UINT_MAX &&
        0 <= d0_orig && d0_orig <= UINT_MAX &&
        0 <= di_orig && di_orig <= UINT_MAX &&
        (di_orig + UINT_MOD) * (UINT_MOD * d1_orig) <=
          Z::pow(UINT_MOD, 3) - 1 &&
        Z::pow(UINT_MOD, 3) - 1 <
          (di_orig + UINT_MOD + 1) * (UINT_MOD * d1_orig) &&
        -1 <= nn && nn < nn0 &&
        nn0 > 0 && nn0 <= INT_MAX &&
        Zlength(l_np) == nn0 &&
        Zlength(l_cur) == nn0 &&
        Zlength(l_done) == nn0 - (nn + 1) &&
        list_within_bound(UINT_MOD, l_np) &&
        list_within_bound(UINT_MOD, l_cur) &&
        list_within_bound(UINT_MOD, l_done) &&
        list_to_Z(UINT_MOD, l_done) == qv_done &&
        0 <= carry && carry <= UINT_MAX &&
        0 <= r && r < d1_orig &&
        carry * Z::pow(UINT_MOD, nn0) + list_to_Z(UINT_MOD, l_cur) ==
          list_to_Z(UINT_MOD, l_done) * Z::pow(UINT_MOD, nn + 1) * d1_orig +
          r * Z::pow(UINT_MOD, nn + 1) +
          list_to_Z(UINT_MOD, sublist(0, nn + 1, l_cur)) &&
        ((shift_orig == 0 && carry == 0 && l_cur == l_np &&
          np == np_orig && tp == 0 && tn == 0 &&
          UIntArray::full(np, nn0, l_cur) *
          ((qp == 0 && emp) ||
           (qp != 0 &&
            UIntArray::undef_seg(qp, 0, nn + 1) *
            UIntArray::seg(qp, nn + 1, nn0, l_done)))) ||
         (shift_orig > 0 && qp0 != 0 &&
          np == qp && tp == qp && tn == 0 &&
          carry * Z::pow(UINT_MOD, nn0) + list_to_Z(UINT_MOD, l_cur) ==
            list_to_Z(UINT_MOD, l_np) * Z::pow(2, shift_orig) &&
          UIntArray::seg(np, 0, nn + 1, sublist(0, nn + 1, l_cur)) *
          UIntArray::seg(qp, nn + 1, nn0, l_done) *
          UIntArray::full(np_orig, nn0, l_np)) ||
         (shift_orig > 0 && qp0 == 0 &&
          np == tp && tn == nn0 &&
          carry * Z::pow(UINT_MOD, nn0) + list_to_Z(UINT_MOD, l_cur) ==
            list_to_Z(UINT_MOD, l_np) * Z::pow(2, shift_orig) &&
          UIntArray::full(np, nn0, l_cur) *
          UIntArray::full(np_orig, nn0, l_np))) *
        store(&(inv->shift), shift_orig) *
        store(&(inv->d1), d1_orig) *
        undef_data_at(&(inv->d0), unsigned int) *
        store(&(inv->di), di_orig)
  */
	  while (nn >= 0)
	    {
		      unsigned int q;
		      gmp_udiv_qrnnd_preinv(&q, &r, r, np[nn], d, di);
		      if (qp != (void *)0)
		        /*@ Assert exists shift_orig d1_orig d0_orig di_orig l_cur l_done qv_done carry r_old qv rv,
		              d == d1_orig &&
		              di == di_orig &&
		              qp0 == qp && np0 == np_orig && inv0 == inv &&
		              0 < d_orig &&
		              0 <= shift_orig && shift_orig < 32 &&
		              d1_orig == d_orig * Z::pow(2, shift_orig) &&
		              d_orig * Z::pow(2, shift_orig) < UINT_MOD &&
		              UINT_MOD / 2 <= d1_orig && d1_orig <= UINT_MAX &&
		              0 <= d0_orig && d0_orig <= UINT_MAX &&
		              0 <= di_orig && di_orig <= UINT_MAX &&
		              (di_orig + UINT_MOD) * (UINT_MOD * d1_orig) <=
		                Z::pow(UINT_MOD, 3) - 1 &&
		              Z::pow(UINT_MOD, 3) - 1 <
		                (di_orig + UINT_MOD + 1) * (UINT_MOD * d1_orig) &&
		              0 <= nn && nn < nn0 &&
		              nn0 > 0 && nn0 <= INT_MAX &&
		              Zlength(l_np) == nn0 &&
		              Zlength(l_cur) == nn0 &&
		              Zlength(l_done) == nn0 - (nn + 1) &&
		              list_within_bound(UINT_MOD, l_np) &&
		              list_within_bound(UINT_MOD, l_cur) &&
		              list_within_bound(UINT_MOD, l_done) &&
		              list_to_Z(UINT_MOD, l_done) == qv_done &&
		              0 <= carry && carry <= UINT_MAX &&
		              0 <= r_old && r_old < d1_orig &&
		              0 <= qv && qv <= UINT_MAX &&
		              0 <= rv && rv < d1_orig &&
		              qp0 != 0 &&
		              carry * Z::pow(UINT_MOD, nn0) + list_to_Z(UINT_MOD, l_cur) ==
		                list_to_Z(UINT_MOD, l_done) * Z::pow(UINT_MOD, nn + 1) * d1_orig +
		                r_old * Z::pow(UINT_MOD, nn + 1) +
		                list_to_Z(UINT_MOD, sublist(0, nn + 1, l_cur)) &&
		              ((shift_orig == 0 && carry == 0 && l_cur == l_np &&
		                np == np_orig && tp == 0 && tn == 0 &&
		                r_old * UINT_MOD + l_cur[nn] == qv * d1_orig + rv &&
		                UIntArray::full(np, nn0, l_cur) *
		                UIntArray::undef_seg(qp, 0, nn + 1) *
		                UIntArray::seg(qp, nn + 1, nn0, l_done)) ||
		               (shift_orig > 0 &&
		                np == qp && tp == qp && tn == 0 &&
		                carry * Z::pow(UINT_MOD, nn0) + list_to_Z(UINT_MOD, l_cur) ==
		                  list_to_Z(UINT_MOD, l_np) * Z::pow(2, shift_orig) &&
		                r_old * UINT_MOD + sublist(0, nn + 1, l_cur)[nn - 0] ==
		                  qv * d1_orig + rv &&
		                UIntArray::seg(qp, 0, nn + 1, sublist(0, nn + 1, l_cur)) *
		                UIntArray::seg(qp, nn + 1, nn0, l_done) *
		                UIntArray::full(np_orig, nn0, l_np))) *
		              store_uint(&q, qv) *
		              store_uint(&r, rv) *
		              store(&(inv->shift), shift_orig) *
		              store(&(inv->d1), d1_orig) *
		              undef_data_at(&(inv->d0), unsigned int) *
		              store(&(inv->di), di_orig)
		        */
		        qp[nn] = q;
	      nn = nn - 1;
    }
  /*@ Assert exists shift_orig d1_orig d0_orig di_orig l_cur l_q qv carry tmp_val tmp_len,
        d == d1_orig &&
        di == di_orig &&
        qp0 == qp && np0 == np_orig && inv0 == inv &&
        0 < d_orig &&
        0 <= shift_orig && shift_orig < 32 &&
        d1_orig == d_orig * Z::pow(2, shift_orig) &&
        d_orig * Z::pow(2, shift_orig) < UINT_MOD &&
        UINT_MOD / 2 <= d1_orig && d1_orig <= UINT_MAX &&
        0 <= d0_orig && d0_orig <= UINT_MAX &&
        0 <= di_orig && di_orig <= UINT_MAX &&
        (di_orig + UINT_MOD) * (UINT_MOD * d1_orig) <=
          Z::pow(UINT_MOD, 3) - 1 &&
        Z::pow(UINT_MOD, 3) - 1 <
          (di_orig + UINT_MOD + 1) * (UINT_MOD * d1_orig) &&
        nn == -1 &&
        nn0 > 0 && nn0 <= INT_MAX &&
        Zlength(l_np) == nn0 &&
        Zlength(l_cur) == nn0 &&
        Zlength(l_q) == nn0 &&
        list_within_bound(UINT_MOD, l_np) &&
        list_within_bound(UINT_MOD, l_cur) &&
        list_within_bound(UINT_MOD, l_q) &&
        list_to_Z(UINT_MOD, l_q) == qv &&
        carry * Z::pow(UINT_MOD, nn0) + list_to_Z(UINT_MOD, l_cur) ==
          qv * d1_orig + r &&
        0 <= r && r < d1_orig &&
        ((shift_orig == 0 && carry == 0 && l_cur == l_np &&
          np == np_orig && tp == 0 && tn == 0 &&
          ((qp0 == 0 && emp) ||
           (qp0 != 0 && UIntArray::full(qp0, nn0, l_q))) *
          UIntArray::full(np_orig, nn0, l_np)) ||
         (shift_orig > 0 && qp0 != 0 &&
          np == qp0 && tp == qp0 && tn == 0 &&
          carry * Z::pow(UINT_MOD, nn0) + list_to_Z(UINT_MOD, l_cur) ==
            list_to_Z(UINT_MOD, l_np) * Z::pow(2, shift_orig) &&
          UIntArray::full(qp0, nn0, l_q) *
          UIntArray::full(np_orig, nn0, l_np)) ||
         (shift_orig > 0 && qp0 == 0 &&
          np == tp && tn == nn0 &&
          carry * Z::pow(UINT_MOD, nn0) + list_to_Z(UINT_MOD, l_cur) ==
            list_to_Z(UINT_MOD, l_np) * Z::pow(2, shift_orig) &&
          0 <= tmp_len && tmp_len <= tn &&
          UIntArray::full(np_orig, nn0, l_np) *
          mpd_store_Z_compact(UINT_MOD, tp, tmp_val, tmp_len) *
          UIntArray::undef_seg(tp, tmp_len, tn))) *
        store(&(inv->shift), shift_orig) *
        store(&(inv->d1), d1_orig) *
        undef_data_at(&(inv->d0), unsigned int) *
        store(&(inv->di), di_orig)
  */
  if (tn)
    gmp_free_limbs(tp, tn);

  return r >> inv->shift;
}
