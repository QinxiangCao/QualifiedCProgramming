#include "fme_ge_gmp/gmp/gmp_def.h"
/*@ include strategies "mpz_div_qr.strategies" */

/*@ Extern Coq (optional_q_undef : Z -> Z -> Assertion)
               (optional_q_full : Z -> Z -> list Z -> Assertion) */
/*@ Extern Coq (Zmax : Z -> Z -> Z)
               (store_Z_read0 : Z -> Z -> Assertion)
               (mpd_read0_data : list Z -> list Z)
               (mpd_store_Z_compact_read0 : Z -> Z -> Z -> Assertion) */
/*@ include strategies "mpz_tdiv_r_read0.strategies" */

enum mpz_div_round_mode { GMP_DIV_FLOOR, GMP_DIV_CEIL, GMP_DIV_TRUNC };

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

mpz_ptr malloc_mpz_struct()
/*@ Require emp
  Ensure __return != 0 &&
         undef_data_at(&(__return->_mp_alloc)) *
         undef_data_at(&(__return->_mp_size)) *
         undef_data_at(&(__return->_mp_d))
*/;

void free_mpz_struct(mpz_ptr x)
/*@ With size cap ptr
  Require x->_mp_size == size &&
          x->_mp_alloc == cap &&
          x->_mp_d == ptr
  Ensure emp
*/;

void mpz_init2(mpz_ptr x, unsigned long long bits)
/*@
  With alloc
  Require
    bits == alloc * 32 &&
    alloc > 0 &&
    alloc <= INT_MAX &&
    undef_data_at(&(x->_mp_alloc)) *
    undef_data_at(&(x->_mp_size)) *
    undef_data_at(&(x->_mp_d))
  Ensure exists ptr,
    ptr != 0 &&
    x->_mp_alloc == alloc &&
    x->_mp_size == 0 &&
    x->_mp_d == ptr &&
    UIntArray::undef_full(ptr, alloc)
*/;

void mpz_init_set(mpz_t r, const mpz_t x)
/*@
  With z
  Require
    undef_data_at(&(r->_mp_alloc)) *
    undef_data_at(&(r->_mp_size)) *
    undef_data_at(&(r->_mp_d)) *
    store_Z(x, z)
  Ensure
    store_Z(r, z) * store_Z(x, z)
*/;

void mpz_clear (mpz_t r)
/*@
  With
    n
  Require
    store_Z(r, n)
  Ensure
    exists size cap ptr,
      r -> _mp_size == size && r -> _mp_alloc == cap && r -> _mp_d == ptr
*/;

void int_swap(int *x, int *y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x == py && *y == px
*/;

void mp_ptr_swap(unsigned int **x, unsigned int **y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x == py && *y == px
*/;

void
mpz_swap (mpz_t u, mpz_t v)
/*@ plain
  With
    n m
  Require
    store_Z(u, n) * store_Z(v, m)
  Ensure
    store_Z(u, m) * store_Z(v, n)
*/;

void
mpz_swap (mpz_t u, mpz_t v)
/*@ u_read0
  With
    n m
  Require
    store_Z_read0(u, n) * store_Z(v, m)
  Ensure
    store_Z(u, m) * store_Z_read0(v, n)
*/
;

void
mpz_swap (mpz_t u, mpz_t v)
/*@ u_read0 */
{
  /*@ Assert exists uptr usize ucap vptr vsize vcap,
      u == u@pre &&
      v == v@pre &&
      Zabs(usize) <= ucap &&
      same_sign(n, usize) &&
      Zabs(vsize) <= vcap &&
      same_sign(m, vsize) &&
      mpd_store_Z_compact_read0(uptr, Zabs(n), Zabs(usize)) *
      UIntArray::undef_seg(uptr, Zmax(Zabs(usize), 1), ucap) *
      store(&(u->_mp_size), usize) *
      store(&(u->_mp_alloc), ucap) *
      store(&(u->_mp_d), unsigned int *, uptr) *
      mpd_store_Z_compact(UINT_MOD, vptr, Zabs(m), Zabs(vsize)) *
      UIntArray::undef_seg(vptr, Zabs(vsize), vcap) *
      store(&(v->_mp_size), vsize) *
      store(&(v->_mp_alloc), vcap) *
      store(&(v->_mp_d), unsigned int *, vptr)
  */
  int_swap (&u->_mp_alloc, &v->_mp_alloc);
  mp_ptr_swap(&u->_mp_d, &v->_mp_d);
  int_swap (&u->_mp_size, &v->_mp_size);
  /*@ Assert
      u == u@pre && v == v@pre &&
      store_Z(u, m) * store_Z_read0(v, n)
  */
}

void mpz_set(mpz_t rop, const mpz_t op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure store_Z(rop, z) * store_Z(op, z)
*/
/*@ eq
  With z
  Require rop == op && store_Z(op, z)
  Ensure rop == op && store_Z(op, z)
*/;

void mpz_set_ui(mpz_t r, unsigned long x);

void mpz_set_si(mpz_t r, long x);

void mpz_add(mpz_t r, const mpz_t a, const mpz_t b);

void mpz_sub(mpz_t r, const mpz_t a, const mpz_t b);

void mpz_add_ui(mpz_t r, const mpz_t a, unsigned long b);

void mpz_sub_ui(mpz_t r, const mpz_t a, unsigned long b);

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

int
mpn_normalized_size(unsigned int *xp, int n)
/*@ read0
  With val
  Require
    n > 0 &&
    mpd_store_Z(UINT_MOD, xp, val, n)
  Ensure
    0 <= __return && __return <= n &&
    mpd_store_Z_compact_read0(xp, val, __return) *
    UIntArray::undef_seg(xp, Zmax(__return, 1), n)
*/
{
  /*@
    mpd_store_Z(UINT_MOD, xp, val, n)
    which implies
    exists l,
      list_to_Z(UINT_MOD, l) == val &&
      list_within_bound(UINT_MOD, l) &&
      Zlength(l) == n &&
      UIntArray::full(xp, n, l)
  */
  /*@ Given l */
  /*@ Inv
      xp == xp@pre &&
      n@pre > 0 &&
      n >= 0 &&
      n <= n@pre &&
      normalized_size_read0_guard(n, l) &&
      list_to_Z(UINT_MOD, sublist(0, n, l)) == val &&
      list_within_bound(UINT_MOD, l) &&
      Zlength(l) == n@pre &&
      UIntArray::full(xp@pre, n@pre, l)
  */
  while (n > 0 && xp[n-1] == 0)
    --n;

  /*@ Assert
      xp == xp@pre &&
      n@pre > 0 &&
      n >= 0 &&
      n <= n@pre &&
      normalized_size_read0_guard(n, l) &&
      list_to_Z(UINT_MOD, sublist(0, n, l)) == val &&
      list_within_bound(UINT_MOD, l) &&
      Zlength(l) == n@pre &&
      last(sublist(0, n, l), 1) >= 1 &&
      UIntArray::full(xp@pre, n@pre, l)
  */
  return n;
}

void mpn_div_qr(unsigned int *qp, unsigned int *np,
                int nn, unsigned int *dp, int dn)
/*@
  With qp0 np0 dp0 nn0 dn0 l_np d_orig
  Require qp0 == qp && np0 == np && dp0 == dp &&
          nn0 == nn && dn0 == dn &&
          dn > 0 && dn <= nn && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          list_within_bound(UINT_MOD, l_np) &&
          optional_q_undef(qp, nn - dn + 1) *
          UIntArray::full(np, nn, l_np) *
          mpd_store_Z_compact(UINT_MOD, dp, d_orig, dn)
  Ensure exists l_q l_rem l_tail qv rv,
          Zlength(l_q) == nn0 - dn0 + 1 &&
          Zlength(l_rem) == dn0 &&
          Zlength(l_tail) == nn0 - dn0 &&
          list_within_bound(UINT_MOD, l_q) &&
          list_within_bound(UINT_MOD, l_rem) &&
          list_within_bound(UINT_MOD, l_tail) &&
          list_to_Z(UINT_MOD, l_q) == qv &&
          list_to_Z(UINT_MOD, l_rem) == rv &&
          list_to_Z(UINT_MOD, l_np) == qv * d_orig + rv &&
          0 <= rv && rv < d_orig &&
          optional_q_full(qp0, nn0 - dn0 + 1, l_q) *
          UIntArray::seg(np0, 0, dn0, l_rem) *
          UIntArray::seg(np0, dn0, nn0, l_tail) *
          mpd_store_Z_compact(UINT_MOD, dp0, d_orig, dn0)
*/;

/* Allows q or r to be zero. Returns 1 iff remainder is non-zero. */
static int
mpz_div_qr(mpz_ptr q, mpz_ptr r,
           mpz_srcptr n, mpz_srcptr d, enum mpz_div_round_mode mode)
/*@ nonalias
  With q0 r0 n0 d0 mode0 old_q old_r zn zd
  Require
    q == q0 &&
    r == r0 &&
    n == n0 &&
    d == d0 &&
    mode == mode0 &&
    zd != 0 &&
    mode0 == GMP_DIV_TRUNC &&
    store_Z(n0, zn) * store_Z(d0, zd) *
    optional_store_Z(q0, old_q) *
    optional_store_Z(r0, old_r)
  Ensure exists qv rv,
    mpz_div_qr_math(mode0, zn, zd, qv, rv) &&
    0 <= __return && __return <= 1 &&
    mpz_div_qr_ret_ok(__return, rv) &&
    store_Z(n0, zn) * store_Z(d0, zd) *
    optional_store_Z(q0, qv) *
    optional_store_Z(r0, rv)
*/
;

static int
mpz_div_qr(mpz_ptr q, mpz_ptr r,
           mpz_srcptr n, mpz_srcptr d, enum mpz_div_round_mode mode)
/*@ r_eq_n_read0
  With q0 r0 n0 d0 mode0 old_q zn zd
  Require
    q == q0 &&
    r == r0 &&
    n == n0 &&
    d == d0 &&
    mode == mode0 &&
    r0 == n0 &&
    n0 != 0 &&
    zn != 0 &&
    zd != 0 &&
    mode0 == GMP_DIV_TRUNC &&
    store_Z(n0, zn) * store_Z(d0, zd) *
    optional_store_Z(q0, old_q)
  Ensure exists qv rv,
    r0 == n0 &&
    mpz_div_qr_math(mode0, zn, zd, qv, rv) &&
    0 <= __return && __return <= 1 &&
    mpz_div_qr_ret_ok(__return, rv) &&
    store_Z_read0(n0, rv) * store_Z(d0, zd) *
    optional_store_Z(q0, qv)
*/
;

static int
mpz_div_qr(mpz_ptr q, mpz_ptr r,
           mpz_srcptr n, mpz_srcptr d, enum mpz_div_round_mode mode)
/*@ nonalias */
/*@ r_eq_n_read0 */
{
  int ns;
  int ds;
  int nn;
  int dn;
  int qs;

  /*@ Assert
      q == q0_nonalias && r == r0_nonalias && n == n0_nonalias &&
      d == d0_nonalias && mode == mode0_nonalias &&
      zd_nonalias != 0 && mode == GMP_DIV_TRUNC &&
      store_Z(n, zn_nonalias) *
      store_Z(d, zd_nonalias) *
      optional_store_Z(q, old_q_nonalias) *
      optional_store_Z(r, old_r_nonalias) *
      has_permission(&qs) *
      has_permission(&dn) *
      has_permission(&nn) *
      has_permission(&ds) *
      has_permission(&ns)
      $ nonalias
  */
  /*@ Assert
      q == q0_r_eq_n_read0 && r == r0_r_eq_n_read0 && n == n0_r_eq_n_read0 &&
      d == d0_r_eq_n_read0 && mode == mode0_r_eq_n_read0 &&
      r == n && n != 0 && zn_r_eq_n_read0 != 0 &&
      zd_r_eq_n_read0 != 0 && mode == GMP_DIV_TRUNC &&
      store_Z(n, zn_r_eq_n_read0) *
      store_Z(d, zd_r_eq_n_read0) *
      optional_store_Z(q, old_q_r_eq_n_read0) *
      has_permission(&qs) *
      has_permission(&dn) *
      has_permission(&nn) *
      has_permission(&ds) *
	      has_permission(&ns)
	      $ r_eq_n_read0
	  */

	  ns = n->_mp_size;
  ds = d->_mp_size;

  /*@
    is_compact_Z(UINT_MOD, Zabs(zn_nonalias), Zabs(ns)) &&
    is_compact_Z(UINT_MOD, Zabs(zd_nonalias), Zabs(ds))
    $ nonalias
  */
  /*@
    is_compact_Z(UINT_MOD, Zabs(zn_r_eq_n_read0), Zabs(ns)) &&
    is_compact_Z(UINT_MOD, Zabs(zd_r_eq_n_read0), Zabs(ds))
    $ r_eq_n_read0
  */

  if (ns == 0)
    {
      if (q)
        q->_mp_size = 0;

      if (r)
        r->_mp_size = 0;
      return 0;
    }

  nn = gmp_abs(ns);
  dn = gmp_abs(ds);

  qs = ds ^ ns;

  if (nn < dn)
    {
      if (mode == GMP_DIV_CEIL && qs >= 0)
        {
          /*@ Branch clear all */
          /* q = 1, r = n - d */
          if (r)
            mpz_sub(r, n, d);

          if (q)
            mpz_set_ui(q, 1);
        }
      else if (mode == GMP_DIV_FLOOR && qs < 0)
        {
          /*@ Branch clear all */
          /* q = -1, r = n + d */
          if (r)
            mpz_add(r, n, d);

          if (q)
            mpz_set_si(q, -1);
        }
      else
	        {
	          /* q = 0, r = d */
          if (r)
            mpz_set(r, n)
              /*@ where (neq) old = old_r_nonalias, z = zn_nonalias $ nonalias
	                  where (eq) z = zn_r_eq_n_read0 $ r_eq_n_read0 */;

          if (q)
            q->_mp_size = 0;
        }

      return 1;
    }
  else
    {
      unsigned int *np;
      unsigned int *qp;
      int qn;
      int rn;
      mpz_ptr tq;
      mpz_ptr tr;

      tr = malloc_mpz_struct();
      mpz_init_set(tr, n)
        /*@ where z = zn_nonalias $ nonalias
            where z = zn_r_eq_n_read0 $ r_eq_n_read0 */;
      np = tr->_mp_d;

      qn = nn - dn + 1;

      /*@ Destruct $ nonalias r_eq_n_read0 with
          nonalias_q r_eq_n_q: q != 0;
          nonalias_noq r_eq_n_noq: q == 0
      */
      if (q)
        {
          tq = malloc_mpz_struct();
          mpz_init2(tq, ((unsigned long long) qn) * ((unsigned long long) 32))
            /*@ where alloc = qn */;
          qp = tq->_mp_d;
        }
      else
        qp = (void *)0;

      /*@ Assert exists l_np tr_size tr_cap d_size d_cap dptr nn_g dn_g zd_g,
          q == q0_nonalias && r == r0_nonalias && n == n0_nonalias &&
          d == d0_nonalias && mode == mode0_nonalias &&
          nn_g == nn && dn_g == dn && zd_g == zd_nonalias &&
          q != 0 && tq != 0 && qp != 0 &&
          qn == nn_g - dn_g + 1 &&
          nn_g >= dn_g && dn_g > 0 && nn_g <= INT_MAX &&
          Zlength(l_np) == nn_g &&
          list_within_bound(UINT_MOD, l_np) &&
          list_to_Z(UINT_MOD, l_np) == Zabs(zn_nonalias) &&
          is_compact_Z(UINT_MOD, Zabs(zn_nonalias), nn_g) &&
          is_compact_Z(UINT_MOD, Zabs(zd_g), dn_g) &&
          zn_nonalias != 0 &&
          ns == tr_size && ds == d_size && qs == (ds ^ ns) &&
          same_sign(zn_nonalias, tr_size) &&
          Zabs(tr_size) == nn_g &&
          Zabs(tr_size) <= tr_cap &&
          same_sign(zd_g, d_size) &&
          Zabs(d_size) == dn_g &&
          Zabs(d_size) <= d_cap &&
          zd_g != 0 &&
          mode == GMP_DIV_TRUNC &&
          optional_q_undef(qp, nn_g - dn_g + 1) *
          UIntArray::full(np, nn_g, l_np) *
          UIntArray::undef_seg(np, nn_g, tr_cap) *
          store(&(tr->_mp_size), tr_size) *
          store(&(tr->_mp_alloc), tr_cap) *
          store(&(tr->_mp_d), unsigned int *, np) *
          store(&(tq->_mp_size), 0) *
          store(&(tq->_mp_alloc), qn) *
          store(&(tq->_mp_d), unsigned int *, qp) *
          mpd_store_Z_compact(UINT_MOD, dptr, Zabs(zd_g), dn_g) *
          UIntArray::undef_seg(dptr, dn_g, d_cap) *
          store(&(d->_mp_size), d_size) *
          store(&(d->_mp_alloc), d_cap) *
          store(&(d->_mp_d), unsigned int *, dptr) *
          store_Z(n, zn_nonalias) *
          optional_store_Z(q, old_q_nonalias) *
          optional_store_Z(r, old_r_nonalias) *
          has_permission(&rn)
          $ nonalias_q
      */
      /*@ Assert exists l_np tr_size tr_cap d_size d_cap dptr nn_g dn_g zd_g,
          q == q0_nonalias && r == r0_nonalias && n == n0_nonalias &&
          d == d0_nonalias && mode == mode0_nonalias &&
          nn_g == nn && dn_g == dn && zd_g == zd_nonalias &&
          q == 0 && qp == 0 &&
          qn == nn_g - dn_g + 1 &&
          nn_g >= dn_g && dn_g > 0 && nn_g <= INT_MAX &&
          Zlength(l_np) == nn_g &&
          list_within_bound(UINT_MOD, l_np) &&
          list_to_Z(UINT_MOD, l_np) == Zabs(zn_nonalias) &&
          is_compact_Z(UINT_MOD, Zabs(zn_nonalias), nn_g) &&
          is_compact_Z(UINT_MOD, Zabs(zd_g), dn_g) &&
          zn_nonalias != 0 &&
          ns == tr_size && ds == d_size && qs == (ds ^ ns) &&
          same_sign(zn_nonalias, tr_size) &&
          Zabs(tr_size) == nn_g &&
          Zabs(tr_size) <= tr_cap &&
          same_sign(zd_g, d_size) &&
          Zabs(d_size) == dn_g &&
          Zabs(d_size) <= d_cap &&
          zd_g != 0 &&
          mode == GMP_DIV_TRUNC &&
          optional_q_undef(qp, nn_g - dn_g + 1) *
          UIntArray::full(np, nn_g, l_np) *
          UIntArray::undef_seg(np, nn_g, tr_cap) *
          store(&(tr->_mp_size), tr_size) *
          store(&(tr->_mp_alloc), tr_cap) *
          store(&(tr->_mp_d), unsigned int *, np) *
          mpd_store_Z_compact(UINT_MOD, dptr, Zabs(zd_g), dn_g) *
          UIntArray::undef_seg(dptr, dn_g, d_cap) *
          store(&(d->_mp_size), d_size) *
          store(&(d->_mp_alloc), d_cap) *
          store(&(d->_mp_d), unsigned int *, dptr) *
          store_Z(n, zn_nonalias) *
          optional_store_Z(q, old_q_nonalias) *
          optional_store_Z(r, old_r_nonalias) *
          has_permission(&tq) *
          has_permission(&rn)
          $ nonalias_noq
      */
      /*@ Assert exists l_np tr_size tr_cap d_size d_cap dptr nn_g dn_g zd_g,
          q == q0_r_eq_n_read0 && r == r0_r_eq_n_read0 && n == n0_r_eq_n_read0 &&
          d == d0_r_eq_n_read0 && mode == mode0_r_eq_n_read0 &&
          nn_g == nn && dn_g == dn && zd_g == zd_r_eq_n_read0 &&
          r == n && n != 0 &&
          zn_r_eq_n_read0 != 0 &&
          q != 0 && tq != 0 && qp != 0 &&
          qn == nn_g - dn_g + 1 &&
          nn_g >= dn_g && dn_g > 0 && nn_g <= INT_MAX &&
          Zlength(l_np) == nn_g &&
          list_within_bound(UINT_MOD, l_np) &&
          list_to_Z(UINT_MOD, l_np) == Zabs(zn_r_eq_n_read0) &&
          is_compact_Z(UINT_MOD, Zabs(zn_r_eq_n_read0), nn_g) &&
          is_compact_Z(UINT_MOD, Zabs(zd_g), dn_g) &&
          zn_r_eq_n_read0 != 0 &&
          ns == tr_size && ds == d_size && qs == (ds ^ ns) &&
          same_sign(zn_r_eq_n_read0, tr_size) &&
          Zabs(tr_size) == nn_g &&
          Zabs(tr_size) <= tr_cap &&
          same_sign(zd_g, d_size) &&
          Zabs(d_size) == dn_g &&
          Zabs(d_size) <= d_cap &&
          zd_g != 0 &&
          mode == GMP_DIV_TRUNC &&
          optional_q_undef(qp, nn_g - dn_g + 1) *
          UIntArray::full(np, nn_g, l_np) *
          UIntArray::undef_seg(np, nn_g, tr_cap) *
          store(&(tr->_mp_size), tr_size) *
          store(&(tr->_mp_alloc), tr_cap) *
          store(&(tr->_mp_d), unsigned int *, np) *
          store(&(tq->_mp_size), 0) *
          store(&(tq->_mp_alloc), qn) *
          store(&(tq->_mp_d), unsigned int *, qp) *
          mpd_store_Z_compact(UINT_MOD, dptr, Zabs(zd_g), dn_g) *
          UIntArray::undef_seg(dptr, dn_g, d_cap) *
          store(&(d->_mp_size), d_size) *
          store(&(d->_mp_alloc), d_cap) *
          store(&(d->_mp_d), unsigned int *, dptr) *
          store_Z(n, zn_r_eq_n_read0) *
          optional_store_Z(q, old_q_r_eq_n_read0) *
          has_permission(&rn)
          $ r_eq_n_q
      */
      /*@ Assert exists l_np tr_size tr_cap d_size d_cap dptr nn_g dn_g zd_g,
          q == q0_r_eq_n_read0 && r == r0_r_eq_n_read0 && n == n0_r_eq_n_read0 &&
          d == d0_r_eq_n_read0 && mode == mode0_r_eq_n_read0 &&
          nn_g == nn && dn_g == dn && zd_g == zd_r_eq_n_read0 &&
          r == n && n != 0 &&
          zn_r_eq_n_read0 != 0 &&
          q == 0 && qp == 0 &&
          qn == nn_g - dn_g + 1 &&
          nn_g >= dn_g && dn_g > 0 && nn_g <= INT_MAX &&
          Zlength(l_np) == nn_g &&
          list_within_bound(UINT_MOD, l_np) &&
          list_to_Z(UINT_MOD, l_np) == Zabs(zn_r_eq_n_read0) &&
          is_compact_Z(UINT_MOD, Zabs(zn_r_eq_n_read0), nn_g) &&
          is_compact_Z(UINT_MOD, Zabs(zd_g), dn_g) &&
          zn_r_eq_n_read0 != 0 &&
          ns == tr_size && ds == d_size && qs == (ds ^ ns) &&
          same_sign(zn_r_eq_n_read0, tr_size) &&
          Zabs(tr_size) == nn_g &&
          Zabs(tr_size) <= tr_cap &&
          same_sign(zd_g, d_size) &&
          Zabs(d_size) == dn_g &&
          Zabs(d_size) <= d_cap &&
          zd_g != 0 &&
          mode == GMP_DIV_TRUNC &&
          optional_q_undef(qp, nn_g - dn_g + 1) *
          UIntArray::full(np, nn_g, l_np) *
          UIntArray::undef_seg(np, nn_g, tr_cap) *
          store(&(tr->_mp_size), tr_size) *
          store(&(tr->_mp_alloc), tr_cap) *
          store(&(tr->_mp_d), unsigned int *, np) *
          mpd_store_Z_compact(UINT_MOD, dptr, Zabs(zd_g), dn_g) *
          UIntArray::undef_seg(dptr, dn_g, d_cap) *
          store(&(d->_mp_size), d_size) *
          store(&(d->_mp_alloc), d_cap) *
          store(&(d->_mp_d), unsigned int *, dptr) *
          store_Z(n, zn_r_eq_n_read0) *
          optional_store_Z(q, old_q_r_eq_n_read0) *
          has_permission(&tq) *
          has_permission(&rn)
          $ r_eq_n_noq
      */
      /*@ Given l_np tr_size tr_cap d_size d_cap dptr nn_g dn_g zd_g */
      /*@ Branch name
          nonalias_q: q != 0 && zd_nonalias != 0;
          nonalias_noq: q == 0 && zd_nonalias != 0;
          r_eq_n_q: q != 0 && r == n && zd_r_eq_n_read0 != 0;
          r_eq_n_noq: q == 0 && r == n && zd_r_eq_n_read0 != 0
      */
      mpn_div_qr(qp, np, nn, d->_mp_d, dn)
        /*@ where qp0 = qp, np0 = np, dp0 = dptr,
                  nn0 = nn_g, dn0 = dn_g, l_np = l_np,
                  d_orig = Zabs(zd_g) $ nonalias_q nonalias_noq
            where qp0 = qp, np0 = np, dp0 = dptr,
                  nn0 = nn_g, dn0 = dn_g, l_np = l_np,
                  d_orig = Zabs(zd_g) $ r_eq_n_q r_eq_n_noq */;
      /*@ Given l_q l_rem l_tail qv rv */

      /*@
        same_sign(zd_g, d_size) &&
        Zabs(d_size) == dn_g &&
        Zabs(d_size) <= d_cap &&
        mpd_store_Z_compact(UINT_MOD, dptr, Zabs(zd_g), dn_g) *
        UIntArray::undef_seg(dptr, dn_g, d_cap) *
        store(&(d->_mp_size), d_size) *
        store(&(d->_mp_alloc), d_cap) *
        store(&(d->_mp_d), unsigned int *, dptr)
        $ nonalias_q nonalias_noq r_eq_n_q r_eq_n_noq
        which implies
        store_Z(d, zd_g)
      */

      if (qp)
        {
          qn -= (qp[qn - 1] == 0);

          tq->_mp_size = qs < 0 ? -qn : qn;
        }
      /*@
          exists qtr,
            same_sign_or_zero(qtr, qs) &&
            Zabs(qtr) == qv &&
            store(&qp, unsigned int *, qp) *
            has_permission(&qn) *
            store_Z(tq, qtr)
          $ nonalias_q
      */
      /*@
          exists qtr,
            same_sign_or_zero(qtr, qs) &&
            Zabs(qtr) == qv &&
            store(&qp, unsigned int *, qp) *
            has_permission(&qn) *
            store_Z(tq, qtr)
          $ r_eq_n_q
      */
      /*@ Branch join nonalias_q into nonalias_q_done with emp */
      /*@ Branch join r_eq_n_q into r_eq_n_q_done with emp */

      rn = mpn_normalized_size(np, dn)
        /*@ where (plain) $ nonalias_q_done nonalias_noq
            where (read0) $ r_eq_n_q_done r_eq_n_noq */;
      tr->_mp_size = ns < 0 ? -rn : rn;
      /*@
          exists rtr,
            same_sign_or_zero(rtr, ns) &&
            Zabs(rtr) == Zabs(zn_nonalias) % Zabs(zd_nonalias) &&
            mpz_div_qr_ret_ok(rn, rtr) &&
            store(&np, unsigned int *, np) *
            store_Z(tr, rtr)
          $ nonalias_q_done
      */
      /*@
          exists rtr,
            same_sign_or_zero(rtr, ns) &&
            Zabs(rtr) == Zabs(zn_nonalias) % Zabs(zd_nonalias) &&
            mpz_div_qr_ret_ok(rn, rtr) &&
            store(&np, unsigned int *, np) *
            store_Z(tr, rtr)
          $ nonalias_noq
      */
      /*@
          exists rtr,
            same_sign_or_zero(rtr, ns) &&
            Zabs(rtr) == Zabs(zn_r_eq_n_read0) % Zabs(zd_r_eq_n_read0) &&
            mpz_div_qr_ret_ok(rn, rtr) &&
            store(&np, unsigned int *, np) *
            store_Z_read0(tr, rtr)
          $ r_eq_n_q_done
      */
      /*@
          exists rtr,
            same_sign_or_zero(rtr, ns) &&
            Zabs(rtr) == Zabs(zn_r_eq_n_read0) % Zabs(zd_r_eq_n_read0) &&
            mpz_div_qr_ret_ok(rn, rtr) &&
            store(&np, unsigned int *, np) *
            store_Z_read0(tr, rtr)
          $ r_eq_n_noq
      */
      /*@ Branch join nonalias_q_done into nonalias_q_rem with emp */
      /*@ Branch join nonalias_noq into nonalias_noq_rem with emp */
      /*@ Branch join r_eq_n_q_done into r_eq_n_q_rem with emp */
      /*@ Branch join r_eq_n_noq into r_eq_n_noq_rem with emp */
      if (mode == GMP_DIV_FLOOR && qs < 0 && rn != 0)
        {
          /*@ Branch clear all */
          if (q)
            {
              mpz_sub_ui(tq, tq, 1);
            }

          if (r)
            {
            mpz_add(tr, tr, d);
            }
        }
      else if (mode == GMP_DIV_CEIL && qs >= 0 && rn != 0)
        {
          /*@ Branch clear all */
          if (q)
            {
              mpz_add_ui(tq, tq, 1);
            }

          if (r)
            {
            mpz_sub(tr, tr, d);
            }
        }

      if (q)
        {
          mpz_swap(tq, q)
            /*@ where (plain) */;
          mpz_clear(tq);
          free_mpz_struct(tq);
        }

      if (r)
        mpz_swap(tr, r)
          /*@ where (plain) $ nonalias_q_rem nonalias_noq_rem
              where (u_read0) $ r_eq_n_q_rem r_eq_n_noq_rem */;

      mpz_clear(tr);
      free_mpz_struct(tr);

      /*@ Branch join nonalias_q_rem nonalias_noq_rem into nonalias_done with Assert
          exists qout rout,
          q == q0_nonalias && r == r0_nonalias && n == n0_nonalias &&
          d == d0_nonalias && mode == mode0_nonalias &&
          mpz_div_qr_math(mode, zn_nonalias, zd_nonalias, qout, rout) &&
          mpz_div_qr_ret_ok(rn, rout) &&
          store_Z(n, zn_nonalias) *
          store_Z(d, zd_nonalias) *
          optional_store_Z(q, qout) *
          optional_store_Z(r, rout) *
          has_permission(&np) *
          has_permission(&qp) *
          has_permission(&qn) *
          has_permission(&tq) *
          has_permission(&tr) *
          has_permission(&nn) *
          has_permission(&dn) *
          has_permission(&qs) *
          has_permission(&ds) *
          has_permission(&ns)
      */
      /*@ Branch join r_eq_n_q_rem r_eq_n_noq_rem into r_eq_n_done with Assert
          exists qout rout,
          q == q0_r_eq_n_read0 && r == r0_r_eq_n_read0 && n == n0_r_eq_n_read0 &&
          d == d0_r_eq_n_read0 && mode == mode0_r_eq_n_read0 &&
          r == n &&
          zn_r_eq_n_read0 != 0 &&
          mpz_div_qr_math(mode, zn_r_eq_n_read0, zd_r_eq_n_read0, qout, rout) &&
          mpz_div_qr_ret_ok(rn, rout) &&
          store_Z_read0(n, rout) *
          store_Z(d, zd_r_eq_n_read0) *
          optional_store_Z(q, qout) *
          has_permission(&np) *
          has_permission(&qp) *
          has_permission(&qn) *
          has_permission(&tq) *
          has_permission(&tr) *
          has_permission(&nn) *
          has_permission(&dn) *
          has_permission(&qs) *
          has_permission(&ds) *
          has_permission(&ns)
      */
      return rn != 0;
    }
}


void
mpz_tdiv_r(mpz_ptr r, mpz_srcptr n, mpz_srcptr d)
/*@ r_eq_n_read0
    With zn zd
    Require
      r == n &&
      n != 0 &&
      zn != 0 &&
      zd != 0 &&
      store_Z(n, zn) * store_Z(d, zd)
    Ensure exists qv rv,
      r == n &&
      mpz_div_qr_math(GMP_DIV_TRUNC, zn, zd, qv, rv) &&
      store_Z_read0(n, rv) * store_Z(d, zd)
  */
{
  /*@ Assert
    r == r@pre &&
	    n == n@pre &&
	    d == d@pre &&
	    r == n &&
	    n != 0 &&
	    zn != 0 &&
	    zd != 0 &&
	    store_Z(n, zn) * store_Z(d, zd) *
	    optional_store_Z(0, 0)
	  */
  mpz_div_qr(0, r, n, d, GMP_DIV_TRUNC)
    /*@ where (r_eq_n_read0) q0 = 0, r0 = r, n0 = n, d0 = d,
               mode0 = GMP_DIV_TRUNC, old_q = 0, zn = zn, zd = zd */;
  /*@ Assert exists qv rv,
    r == r@pre &&
    n == n@pre &&
    d == d@pre &&
    r == n &&
    zn != 0 &&
    mpz_div_qr_math(GMP_DIV_TRUNC, zn, zd, qv, rv) &&
    store_Z_read0(n, rv) * store_Z(d, zd) *
    optional_store_Z(0, qv)
  */
}
