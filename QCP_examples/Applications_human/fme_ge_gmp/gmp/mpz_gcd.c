#include "fme_ge_gmp/gmp/gmp_def.h"
/*@ include strategies "mpz_tdiv_r_read0.strategies" */
/*@ Extern Coq (mpd_read0_data : list Z -> list Z) */

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

void mpz_init(mpz_t x)
/*@
  Require
    undef_data_at(&(x->_mp_alloc)) *
    undef_data_at(&(x->_mp_size)) *
    undef_data_at(&(x->_mp_d))
  Ensure
    store_Z(x, 0)
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

void mpz_abs(mpz_t rop, const mpz_t op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure store_Z(rop, Zabs(z)) * store_Z(op, z)
*/;

static unsigned long long
mpz_make_odd (mpz_ptr r)
/*@
  With z
  Require
    z > 0 &&
    store_Z(r, z)
  Ensure exists odd,
    0 <= __return &&
    odd > 0 &&
    odd % 2 == 1 &&
    z == odd * Z::pow(2, __return) &&
    store_Z(r, odd)
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

enum mpz_div_round_mode { GMP_DIV_FLOOR, GMP_DIV_CEIL, GMP_DIV_TRUNC };

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
  */;

int mpz_cmp(const mpz_t a, const mpz_t b)
/*@ neq
  With za zb
  Require store_Z(a, za) * store_Z(b, zb)
  Ensure
    (za > zb && __return == 1 ||
     za == zb && __return == 0 ||
     za < zb && __return == -1) &&
    store_Z(a, za) * store_Z(b, zb)
*/;

void mpz_sub(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ r_eq_a
  With
    za zb
  Require
    r == a && store_Z(a, za) * store_Z(b, zb)
  Ensure
    store_Z(a, za - zb) * store_Z(b, zb)
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

unsigned int mpn_gcd_11(unsigned int u, unsigned int v)
/*@
  Require 0 <= u && u <= UINT_MAX &&
          0 <= v && v <= UINT_MAX &&
          u + v > 0
  Ensure __return == Zgcd(u, v)
*/;

void
mpz_mul_2exp(mpz_ptr r, mpz_srcptr u, unsigned long long bits)
/*@ eq
  With z
  Require
    r == u &&
    bits >= 0 &&
    mpz_mul_2exp_fits(z, bits) &&
    store_Z(r, z)
  Ensure
    r == u &&
    store_Z(r, z * Z::pow(2, bits))
*/;

void
mpz_gcd (mpz_ptr g, mpz_srcptr u, mpz_srcptr v)
/*@
  With
    old zu zv
  Require
    store_Z(g, old) * store_Z(u, zu) * store_Z(v, zv)
  Ensure
    store_Z(g, Zgcd(zu, zv)) * store_Z(u, zu) * store_Z(v, zv)
*/
{
  mpz_ptr tu, tv;
  unsigned long long uz, vz, gz;

  if (u->_mp_size == 0)
    {
      mpz_abs (g, v) /*@ where (neq) old = old, z = zv */;
      return;
    }
  if (v->_mp_size == 0)
    {
      mpz_abs (g, u) /*@ where (neq) old = old, z = zu */;
      return;
    }

  /*@ Assert
      g == g@pre &&
      u == u@pre &&
      v == v@pre &&
      Zabs(zu) > 0 &&
      Zabs(zv) > 0 &&
      mpz_one_limb_headroom(Zgcd(zu, zv)) &&
      has_permission(&tu) *
      has_permission(&tv) *
      has_permission(&uz) *
      has_permission(&vz) *
      has_permission(&gz) *
      store_Z(g, old) *
      store_Z(u, zu) *
      store_Z(v, zv)
  */
  tu = malloc_mpz_struct();
  tv = malloc_mpz_struct();
  mpz_init (tu);
  mpz_init (tv);

  mpz_abs (tu, u) /*@ where (neq) old = 0, z = zu */;
  uz = mpz_make_odd (tu);
  mpz_abs (tv, v) /*@ where (neq) old = 0, z = zv */;
  vz = mpz_make_odd (tv);
  gz = uz < vz ? uz : vz;

  if (tu->_mp_size < tv->_mp_size)
    mpz_swap (tu, tv) /*@ where (plain) */;

  mpz_tdiv_r (tu, tu, tv) /*@ where (r_eq_n_read0) */;
  if (tu->_mp_size == 0)
    {
      mpz_swap (g, tv) /*@ where (plain) */;
    }
  else
    {
      /*@ Assert exists tu_v tv_v uz_v vz_v gz_v,
          g == g@pre &&
          u == u@pre &&
          v == v@pre &&
          tu != 0 &&
          tv != 0 &&
          uz == uz_v &&
          vz == vz_v &&
          gz == gz_v &&
          gz_v >= 0 &&
          tu_v > 0 &&
          tv_v > 0 &&
          tv_v % 2 == 1 &&
          mpz_mul_2exp_fits(Zgcd(tu_v, tv_v), gz_v) &&
          Zgcd(zu, zv) == Z::pow(2, gz_v) * Zgcd(tu_v, tv_v) &&
          store_Z(tu, tu_v) *
          store_Z(tv, tv_v) *
          store_Z(g, old) *
          store_Z(u, zu) *
          store_Z(v, zv)
      */
      /*@ Inv Assert exists tu_v tv_v uz_v vz_v gz_v,
          g == g@pre &&
          u == u@pre &&
          v == v@pre &&
          tu != 0 &&
          tv != 0 &&
          uz == uz_v &&
          vz == vz_v &&
          gz == gz_v &&
          gz_v >= 0 &&
          tu_v > 0 &&
          tv_v > 0 &&
          tv_v % 2 == 1 &&
          mpz_mul_2exp_fits(Zgcd(tu_v, tv_v), gz_v) &&
          Zgcd(zu, zv) == Z::pow(2, gz_v) * Zgcd(tu_v, tv_v) &&
          store_Z(tu, tu_v) *
          store_Z(tv, tv_v) *
          store_Z(g, old) *
          store_Z(u, zu) *
          store_Z(v, zv)
      */
      while (1)
      {
        int c;

        mpz_make_odd (tu);
        c = mpz_cmp (tu, tv) /*@ where (neq) */;
        if (c == 0)
          {
            mpz_swap (g, tu) /*@ where (plain) */;
            break;
          }
        if (c < 0)
          mpz_swap (tu, tv) /*@ where (plain) */;

        if (tv->_mp_size == 1)
          {
            /*@ Assert exists tu_v tv_v uz_v vz_v gz_v cval,
                g == g@pre &&
                u == u@pre &&
                v == v@pre &&
                c == cval &&
                tu != 0 &&
                tv != 0 &&
                uz == uz_v &&
                vz == vz_v &&
                gz == gz_v &&
                gz_v >= 0 &&
                tu_v > 0 &&
                tv_v > 0 &&
                tv_v <= UINT_MAX &&
                tv_v % 2 == 1 &&
                mpz_mul_2exp_fits(Zgcd(tu_v, tv_v), gz_v) &&
                Zgcd(zu, zv) == Z::pow(2, gz_v) * Zgcd(tu_v, tv_v) &&
                store_Z(tu, tu_v) *
                store_Z(tv, tv_v) *
                store_Z(g, old) *
                store_Z(u, zu) *
                store_Z(v, zv)
            */
            unsigned int *gp;

            mpz_tdiv_r (tu, tu, tv) /*@ where (r_eq_n_read0) */;
            /*@ Assert exists tu_v tv_v uz_v vz_v gz_v cval qv rv gptr gsize gcap,
                g == g@pre &&
                u == u@pre &&
                v == v@pre &&
                c == cval &&
                tu != 0 &&
                tv != 0 &&
                uz == uz_v &&
                vz == vz_v &&
                gz == gz_v &&
                mpz_div_qr_math(2, tu_v, tv_v, qv, rv) &&
                gz_v >= 0 &&
                tu_v > 0 &&
                tv_v > 0 &&
                tv_v <= UINT_MAX &&
                tv_v % 2 == 1 &&
                mpz_mul_2exp_fits(Zgcd(tu_v, tv_v), gz_v) &&
                Zgcd(zu, zv) == Z::pow(2, gz_v) * Zgcd(tu_v, tv_v) &&
                gcap >= 0 &&
                gcap <= INT_MAX &&
                Zabs(gsize) <= gcap &&
                same_sign(old, gsize) &&
                g->_mp_size == gsize &&
                g->_mp_alloc == gcap &&
                g->_mp_d == gptr &&
                store_Z_read0(tu, rv) *
                store_Z(tv, tv_v) *
                has_permission(&gp) *
                mpd_store_Z_compact(UINT_MOD, gptr, Zabs(old), Zabs(gsize)) *
                UIntArray::undef_seg(gptr, Zabs(gsize), gcap) *
                store_Z(u, zu) *
                store_Z(v, zv)
            */
            gp = mrz_realloc_if (g, 1);
            /*@ Assert exists rem tv_val tptr tsize tcap tdata vptr vsize vcap vdata gsize gcap cval uz_v vz_v gz_v,
                g == g@pre &&
                u == u@pre &&
                v == v@pre &&
                c == cval &&
                tu != 0 &&
                tv != 0 &&
                uz == uz_v &&
                vz == vz_v &&
                gz == gz_v &&
                gp == g->_mp_d &&
                gz_v >= 0 &&
                tv_val > 0 &&
                vsize == 1 &&
                gcap >= 0 &&
                gcap <= INT_MAX &&
                Zabs(gsize) <= gcap &&
                same_sign(old, gsize) &&
                0 <= rem &&
                rem <= UINT_MAX &&
                0 <= tv_val &&
                tv_val <= UINT_MAX &&
                Znth(0, mpd_read0_data(tdata), 0) == rem &&
                Znth(0, vdata, 0) == tv_val &&
                Zlength(tdata) == Zabs(tsize) &&
                Zlength(vdata) == 1 &&
                last(tdata, 1) >= 1 &&
                list_within_bound(UINT_MOD, tdata) &&
                list_within_bound(UINT_MOD, vdata) &&
                list_to_Z(UINT_MOD, tdata) == rem &&
                list_to_Z(UINT_MOD, vdata) == tv_val &&
                mpz_mul_2exp_fits(Zgcd(rem, tv_val), gz_v) &&
                Zgcd(zu, zv) == Z::pow(2, gz_v) * Zgcd(rem, tv_val) &&
                tu->_mp_size == tsize &&
                tu->_mp_alloc == tcap &&
                tu->_mp_d == tptr &&
                tv->_mp_size == vsize &&
                tv->_mp_alloc == vcap &&
                tv->_mp_d == vptr &&
                g->_mp_size == gsize &&
                g->_mp_alloc == Z::max(1, gcap) &&
                UIntArray::full(tptr, Zmax(Zabs(tsize), 1), mpd_read0_data(tdata)) *
                UIntArray::undef_seg(tptr, Zmax(Zabs(tsize), 1), tcap) *
                UIntArray::full(vptr, 1, vdata) *
                UIntArray::undef_seg(vptr, 1, vcap) *
                mpd_store_Z_compact(UINT_MOD, gp, Zabs(old), Zabs(gsize)) *
                UIntArray::undef_seg(gp, Zabs(gsize), Z::max(1, gcap)) *
                store_Z(u, zu) *
                store_Z(v, zv)
            */
            /*@ Assert exists rem tv_val tptr tsize tcap tdata vptr vsize vcap vdata gsize gcap cval uz_v vz_v gz_v,
                g == g@pre &&
                u == u@pre &&
                v == v@pre &&
                c == cval &&
                tu != 0 &&
                tv != 0 &&
                uz == uz_v &&
                vz == vz_v &&
                gz == gz_v &&
                gp == g->_mp_d &&
                gz_v >= 0 &&
                tv_val > 0 &&
                vsize == 1 &&
                gcap >= 0 &&
                gcap <= INT_MAX &&
                Zabs(gsize) <= gcap &&
                same_sign(old, gsize) &&
                0 <= rem &&
                rem <= UINT_MAX &&
                0 <= tv_val &&
                tv_val <= UINT_MAX &&
                Znth(0, mpd_read0_data(tdata), 0) == rem &&
                Znth(0, vdata, 0) == tv_val &&
                Zlength(tdata) == Zabs(tsize) &&
                Zlength(vdata) == 1 &&
                last(tdata, 1) >= 1 &&
                list_within_bound(UINT_MOD, tdata) &&
                list_within_bound(UINT_MOD, vdata) &&
                list_to_Z(UINT_MOD, tdata) == rem &&
                list_to_Z(UINT_MOD, vdata) == tv_val &&
                mpz_mul_2exp_fits(Zgcd(rem, tv_val), gz_v) &&
                Zgcd(zu, zv) == Z::pow(2, gz_v) * Zgcd(rem, tv_val) &&
                tu->_mp_size == tsize &&
                tu->_mp_alloc == tcap &&
                tu->_mp_d == tptr &&
                tv->_mp_size == vsize &&
                tv->_mp_alloc == vcap &&
                tv->_mp_d == vptr &&
                g->_mp_size == gsize &&
                g->_mp_alloc == Z::max(1, gcap) &&
                UIntArray::seg(tptr, 0, 1, sublist(0, 1, mpd_read0_data(tdata))) *
                UIntArray::seg(tptr, 1, Zmax(Zabs(tsize), 1), sublist(1, Zmax(Zabs(tsize), 1), mpd_read0_data(tdata))) *
                UIntArray::undef_seg(tptr, Zmax(Zabs(tsize), 1), tcap) *
                UIntArray::seg(vptr, 0, 1, sublist(0, 1, vdata)) *
                UIntArray::undef_seg(vptr, 1, vcap) *
                undef_data_at(gp, unsigned int) *
                UIntArray::undef_seg(gp, 1, Z::max(1, gcap)) *
                store_Z(u, zu) *
                store_Z(v, zv)
            */
            *gp = mpn_gcd_11 (tu->_mp_d[0], tv->_mp_d[0]);

            g->_mp_size = *gp != 0;
            break;
          }
        mpz_sub (tu, tu, tv) /*@ where (r_eq_a) */;
      }
    }
  /*@ Assert exists g_odd tu_final tv_final uz_v vz_v gz_v,
      g == g@pre &&
      u == u@pre &&
      v == v@pre &&
      tu != 0 &&
      tv != 0 &&
      uz == uz_v &&
      vz == vz_v &&
      gz == gz_v &&
      gz_v >= 0 &&
      mpz_mul_2exp_fits(g_odd, gz_v) &&
      Zgcd(zu, zv) == g_odd * Z::pow(2, gz_v) &&
      store_Z(g, g_odd) *
      store_Z(tu, tu_final) *
      store_Z(tv, tv_final) *
      store_Z(u, zu) *
      store_Z(v, zv)
  */
  mpz_clear (tu);
  mpz_clear (tv);
  free_mpz_struct(tu);
  free_mpz_struct(tv);
  mpz_mul_2exp (g, g, gz) /*@ where (eq) */;
}
