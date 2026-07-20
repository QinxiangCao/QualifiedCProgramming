#include "fme_ge_gmp/gmp/gmp_def.h"

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

void
mpz_swap (mpz_t u, mpz_t v)
/*@
  With
    n m
  Require
    store_Z(u, n) * store_Z(v, m)
  Ensure
    store_Z(u, m) * store_Z(v, n)
*/;

unsigned int mpn_mul(unsigned int *rp, unsigned int *up, int un,
                     unsigned int *vp, int vn)
/*@
  With l_src l_vp
  Require un > 0 && vn > 0 && vn <= un &&
          Zlength(l_src) == un &&
          Zlength(l_vp) == vn &&
          list_within_bound(UINT_MOD, l_src) &&
          list_within_bound(UINT_MOD, l_vp) &&
          UIntArray::undef_full(rp, un + vn) *
          UIntArray::full(up, un, l_src) *
          UIntArray::full(vp, vn, l_vp)
  Ensure exists l_out val_out,
          Zlength(l_out) == un + vn &&
          list_within_bound(UINT_MOD, l_out) &&
          list_to_Z(UINT_MOD, l_out) == val_out &&
          val_out == list_to_Z(UINT_MOD, l_src) * list_to_Z(UINT_MOD, l_vp) &&
          UIntArray::full(rp, un + vn, l_out) *
          UIntArray::full(up, un, l_src) *
          UIntArray::full(vp, vn, l_vp)
*/;

void mpz_mul(mpz_ptr rop, mpz_srcptr op1, mpz_srcptr op2)
/*@
  With
    z1 z2
  Require
    rop == op1 &&
    store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    rop == op1 &&
    store_Z(op1, z1 * z2) * store_Z(op2, z2)
*/
{
  int sign;
  int un;
  int vn;
  int rn;
  unsigned int *rp;
  unsigned int *up;
  unsigned int *vp;
  unsigned int high;
  mpz_ptr t;

  un = op1->_mp_size;
  vn = op2->_mp_size;
  if (un == 0 || vn == 0) {
    rop->_mp_size = 0;
    return;
  }

  if ((un < 0 && vn > 0) || (un > 0 && vn < 0)) {
    sign = 1;
  } else {
    sign = 0;
  }

  un = gmp_abs(un);
  vn = gmp_abs(vn);
  rn = un + vn;
  /*@ Assert
        exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap l1 l2,
          rop == rop@pre &&
          rop == op1 &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size, op2size) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          un + vn <= INT_MAX &&
          un == Zabs(op1size) &&
          vn == Zabs(op2size) &&
          op1size != 0 &&
          op2size != 0 &&
          same_sign(z1, op1size) &&
          same_sign(z2, op2size) &&
          rptr == op1ptr &&
          rsize == op1size &&
          rcap == op1cap &&
          Zabs(rsize) <= rcap &&
          rcap >= 0 &&
          rcap <= INT_MAX &&
          Zlength(l1) == un &&
          Zlength(l2) == vn &&
          list_within_bound(UINT_MOD, l1) &&
          list_within_bound(UINT_MOD, l2) &&
          list_to_Z(UINT_MOD, l1) == Zabs(z1) &&
          list_to_Z(UINT_MOD, l2) == Zabs(z2) &&
          last(l1, 1) >= 1 &&
          last(l2, 1) >= 1 &&
          has_permission(&rp) *
          has_permission(&up) *
          has_permission(&vp) *
          has_permission(&high) *
          has_permission(&t) *
          store(&(op1->_mp_d), op1ptr) *
          store(&(op1->_mp_size), op1size) *
          store(&(op1->_mp_alloc), op1cap) *
          UIntArray::full(op1ptr, un, l1) *
          UIntArray::undef_seg(op1ptr, un, op1cap) *
          store(&(op2->_mp_d), op2ptr) *
          store(&(op2->_mp_size), op2size) *
          store(&(op2->_mp_alloc), op2cap) *
          UIntArray::full(op2ptr, vn, l2) *
          UIntArray::undef_seg(op2ptr, vn, op2cap)
  */
  t = malloc_mpz_struct();
  mpz_init2(t, ((unsigned long long)(un + vn)) * ((unsigned long long)32))
    /*@ where alloc = un + vn */;
  rp = t->_mp_d;
  up = op1->_mp_d;
  vp = op2->_mp_d;

  /*@ Assert
        exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap l1 l2,
          rop == rop@pre &&
          rop == op1 &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size, op2size) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          un + vn <= INT_MAX &&
          un == Zabs(op1size) &&
          vn == Zabs(op2size) &&
          op1size != 0 &&
          op2size != 0 &&
          same_sign(z1, op1size) &&
          same_sign(z2, op2size) &&
          rptr == op1ptr &&
          rsize == op1size &&
          rcap == op1cap &&
          Zabs(rsize) <= rcap &&
          Zlength(l1) == un &&
          Zlength(l2) == vn &&
          list_within_bound(UINT_MOD, l1) &&
          list_within_bound(UINT_MOD, l2) &&
          list_to_Z(UINT_MOD, l1) == Zabs(z1) &&
          list_to_Z(UINT_MOD, l2) == Zabs(z2) &&
          last(l1, 1) >= 1 &&
          last(l2, 1) >= 1 &&
          up == op1ptr &&
          vp == op2ptr &&
          t->_mp_size == 0 &&
          t->_mp_alloc == un + vn &&
          t->_mp_d == rp &&
          store(&(op1->_mp_d), op1ptr) *
          store(&(op1->_mp_size), op1size) *
          store(&(op1->_mp_alloc), op1cap) *
          UIntArray::full(op1ptr, un, l1) *
          UIntArray::undef_seg(op1ptr, un, op1cap) *
          store(&(op2->_mp_d), op2ptr) *
          store(&(op2->_mp_size), op2size) *
          store(&(op2->_mp_alloc), op2cap) *
          UIntArray::full(op2ptr, vn, l2) *
          UIntArray::undef_seg(op2ptr, vn, op2cap) *
          has_permission(&high) *
          UIntArray::undef_full(rp, un + vn)
  */
  if (un >= vn) {
    /*@ Given rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap l1 l2 */
    mpn_mul(rp, up, un, vp, vn)
      /*@ where l_src = l1, l_vp = l2 */;
  } else {
    /*@ Assert
        exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap l1 l2,
          rop == rop@pre &&
          rop == op1 &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un < vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size, op2size) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          vn + un <= INT_MAX &&
          un == Zabs(op1size) &&
          vn == Zabs(op2size) &&
          op1size != 0 &&
          op2size != 0 &&
          same_sign(z1, op1size) &&
          same_sign(z2, op2size) &&
          rptr == op1ptr &&
          rsize == op1size &&
          rcap == op1cap &&
          Zabs(rsize) <= rcap &&
          Zlength(l1) == un &&
          Zlength(l2) == vn &&
          list_within_bound(UINT_MOD, l1) &&
          list_within_bound(UINT_MOD, l2) &&
          list_to_Z(UINT_MOD, l1) == Zabs(z1) &&
          list_to_Z(UINT_MOD, l2) == Zabs(z2) &&
          last(l1, 1) >= 1 &&
          last(l2, 1) >= 1 &&
          up == op1ptr &&
          vp == op2ptr &&
          t->_mp_size == 0 &&
          t->_mp_alloc == un + vn &&
          t->_mp_d == rp &&
          store(&(op1->_mp_d), op1ptr) *
          store(&(op1->_mp_size), op1size) *
          store(&(op1->_mp_alloc), op1cap) *
          UIntArray::full(up, un, l1) *
          UIntArray::undef_seg(up, un, op1cap) *
          store(&(op2->_mp_d), op2ptr) *
          store(&(op2->_mp_size), op2size) *
          store(&(op2->_mp_alloc), op2cap) *
          UIntArray::full(vp, vn, l2) *
          UIntArray::undef_seg(vp, vn, op2cap) *
          has_permission(&high) *
          UIntArray::undef_full(rp, vn + un)
    */
    /*@ Given rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap l1 l2 */
    mpn_mul(rp, vp, vn, up, un)
      /*@ where l_src = l2, l_vp = l1 */;
  }

  rn = un + vn;
  high = rp[rn - 1];
  if (high == 0) {
    rn = rn - 1;
  }
  if (sign) {
    rn = -rn;
  }
  t->_mp_size = rn;
  /*@ Assert
        rop == rop@pre &&
        rop == op1 &&
        op1 == op1@pre &&
        op2 == op2@pre &&
        store_Z(op1, z1) *
        store_Z(op2, z2) *
        store_Z(t, z1 * z2) *
        has_permission(&sign) *
        has_permission(&un) *
        has_permission(&vn) *
        has_permission(&rn) *
        has_permission(&rp) *
        has_permission(&up) *
        has_permission(&vp) *
        has_permission(&high)
  */
  mpz_swap(rop, t);
  mpz_clear(t);
  free_mpz_struct(t);
}
