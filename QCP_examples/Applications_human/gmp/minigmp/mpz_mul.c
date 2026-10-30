#include "gmp/minigmp/gmp_def.h"

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

void mpz_clear (mpz_ptr r)
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
mpz_swap (mpz_ptr u, mpz_ptr v)
/*@ plain
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
/*@ neq
  With
    old z1 z2
  Require
    store_Z(rop, old) * store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    store_Z(rop, z1 * z2) * store_Z(op1, z1) * store_Z(op2, z2)
*/
/*@ r_eq_op1
  With
    z1 z2
  Require
    rop == op1 &&
    store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    rop == op1 &&
    store_Z(op1, z1 * z2) * store_Z(op2, z2)
*/
/*@ r_eq_op2
  With
    z1 z2
  Require
    rop == op2 &&
    store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    rop == op2 &&
    store_Z(op1, z1) * store_Z(op2, z1 * z2)
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
        exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq l1_neq l2_neq,
          rop == rop@pre &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size_neq, op2size_neq) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          un + vn <= INT_MAX &&
          un == Zabs(op1size_neq) &&
          vn == Zabs(op2size_neq) &&
          op1size_neq != 0 &&
          op2size_neq != 0 &&
          same_sign(z1_neq, op1size_neq) &&
          same_sign(z2_neq, op2size_neq) &&
          same_sign(old_neq, rsize_neq) &&
          Zabs(rsize_neq) <= rcap_neq &&
          rcap_neq >= 0 &&
          rcap_neq <= INT_MAX &&
          Zlength(l1_neq) == un &&
          Zlength(l2_neq) == vn &&
          list_within_bound(UINT_MOD, l1_neq) &&
          list_within_bound(UINT_MOD, l2_neq) &&
          list_to_Z(UINT_MOD, l1_neq) == Zabs(z1_neq) &&
          list_to_Z(UINT_MOD, l2_neq) == Zabs(z2_neq) &&
          last(l1_neq, 1) >= 1 &&
          last(l2_neq, 1) >= 1 &&
          rop->_mp_size == rsize_neq &&
          rop->_mp_alloc == rcap_neq &&
          rop->_mp_d == rptr_neq &&
          has_permission(&rp) *
          has_permission(&up) *
          has_permission(&vp) *
          has_permission(&high) *
          has_permission(&t) *
          store(&(op1->_mp_d), op1ptr_neq) *
          store(&(op1->_mp_size), op1size_neq) *
          store(&(op1->_mp_alloc), op1cap_neq) *
          UIntArray::full(op1ptr_neq, un, l1_neq) *
          UIntArray::undef_seg(op1ptr_neq, un, op1cap_neq) *
          store(&(op2->_mp_d), op2ptr_neq) *
          store(&(op2->_mp_size), op2size_neq) *
          store(&(op2->_mp_alloc), op2cap_neq) *
          UIntArray::full(op2ptr_neq, vn, l2_neq) *
          UIntArray::undef_seg(op2ptr_neq, vn, op2cap_neq) *
          mpd_store_Z_compact(UINT_MOD, rptr_neq, Zabs(old_neq), Zabs(rsize_neq)) *
          UIntArray::undef_seg(rptr_neq, Zabs(rsize_neq), rcap_neq) $ neq */
  /*@ Assert
        exists rptr_r_eq_op1 rsize_r_eq_op1 rcap_r_eq_op1 op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 l1_r_eq_op1 l2_r_eq_op1,
          rop == rop@pre &&
          rop == op1 &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size_r_eq_op1, op2size_r_eq_op1) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          un + vn <= INT_MAX &&
          un == Zabs(op1size_r_eq_op1) &&
          vn == Zabs(op2size_r_eq_op1) &&
          op1size_r_eq_op1 != 0 &&
          op2size_r_eq_op1 != 0 &&
          same_sign(z1_r_eq_op1, op1size_r_eq_op1) &&
          same_sign(z2_r_eq_op1, op2size_r_eq_op1) &&
          rptr_r_eq_op1 == op1ptr_r_eq_op1 &&
          rsize_r_eq_op1 == op1size_r_eq_op1 &&
          rcap_r_eq_op1 == op1cap_r_eq_op1 &&
          Zabs(rsize_r_eq_op1) <= rcap_r_eq_op1 &&
          rcap_r_eq_op1 >= 0 &&
          rcap_r_eq_op1 <= INT_MAX &&
          Zlength(l1_r_eq_op1) == un &&
          Zlength(l2_r_eq_op1) == vn &&
          list_within_bound(UINT_MOD, l1_r_eq_op1) &&
          list_within_bound(UINT_MOD, l2_r_eq_op1) &&
          list_to_Z(UINT_MOD, l1_r_eq_op1) == Zabs(z1_r_eq_op1) &&
          list_to_Z(UINT_MOD, l2_r_eq_op1) == Zabs(z2_r_eq_op1) &&
          last(l1_r_eq_op1, 1) >= 1 &&
          last(l2_r_eq_op1, 1) >= 1 &&
          has_permission(&rp) *
          has_permission(&up) *
          has_permission(&vp) *
          has_permission(&high) *
          has_permission(&t) *
          store(&(op1->_mp_d), op1ptr_r_eq_op1) *
          store(&(op1->_mp_size), op1size_r_eq_op1) *
          store(&(op1->_mp_alloc), op1cap_r_eq_op1) *
          UIntArray::full(op1ptr_r_eq_op1, un, l1_r_eq_op1) *
          UIntArray::undef_seg(op1ptr_r_eq_op1, un, op1cap_r_eq_op1) *
          store(&(op2->_mp_d), op2ptr_r_eq_op1) *
          store(&(op2->_mp_size), op2size_r_eq_op1) *
          store(&(op2->_mp_alloc), op2cap_r_eq_op1) *
          UIntArray::full(op2ptr_r_eq_op1, vn, l2_r_eq_op1) *
          UIntArray::undef_seg(op2ptr_r_eq_op1, vn, op2cap_r_eq_op1) $ r_eq_op1 */
  /*@ Assert
        exists rptr_r_eq_op2 rsize_r_eq_op2 rcap_r_eq_op2 op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 l1_r_eq_op2 l2_r_eq_op2,
          rop == rop@pre &&
          rop == op2 &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size_r_eq_op2, op2size_r_eq_op2) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          un + vn <= INT_MAX &&
          un == Zabs(op1size_r_eq_op2) &&
          vn == Zabs(op2size_r_eq_op2) &&
          op1size_r_eq_op2 != 0 &&
          op2size_r_eq_op2 != 0 &&
          same_sign(z1_r_eq_op2, op1size_r_eq_op2) &&
          same_sign(z2_r_eq_op2, op2size_r_eq_op2) &&
          rptr_r_eq_op2 == op2ptr_r_eq_op2 &&
          rsize_r_eq_op2 == op2size_r_eq_op2 &&
          rcap_r_eq_op2 == op2cap_r_eq_op2 &&
          Zabs(rsize_r_eq_op2) <= rcap_r_eq_op2 &&
          rcap_r_eq_op2 >= 0 &&
          rcap_r_eq_op2 <= INT_MAX &&
          Zlength(l1_r_eq_op2) == un &&
          Zlength(l2_r_eq_op2) == vn &&
          list_within_bound(UINT_MOD, l1_r_eq_op2) &&
          list_within_bound(UINT_MOD, l2_r_eq_op2) &&
          list_to_Z(UINT_MOD, l1_r_eq_op2) == Zabs(z1_r_eq_op2) &&
          list_to_Z(UINT_MOD, l2_r_eq_op2) == Zabs(z2_r_eq_op2) &&
          last(l1_r_eq_op2, 1) >= 1 &&
          last(l2_r_eq_op2, 1) >= 1 &&
          has_permission(&rp) *
          has_permission(&up) *
          has_permission(&vp) *
          has_permission(&high) *
          has_permission(&t) *
          store(&(op1->_mp_d), op1ptr_r_eq_op2) *
          store(&(op1->_mp_size), op1size_r_eq_op2) *
          store(&(op1->_mp_alloc), op1cap_r_eq_op2) *
          UIntArray::full(op1ptr_r_eq_op2, un, l1_r_eq_op2) *
          UIntArray::undef_seg(op1ptr_r_eq_op2, un, op1cap_r_eq_op2) *
          store(&(op2->_mp_d), op2ptr_r_eq_op2) *
          store(&(op2->_mp_size), op2size_r_eq_op2) *
          store(&(op2->_mp_alloc), op2cap_r_eq_op2) *
          UIntArray::full(op2ptr_r_eq_op2, vn, l2_r_eq_op2) *
          UIntArray::undef_seg(op2ptr_r_eq_op2, vn, op2cap_r_eq_op2) $ r_eq_op2 */
  t = malloc_mpz_struct();
  mpz_init2(t, ((unsigned long long)(un + vn)) * ((unsigned long long)32))
    /*@ where alloc = un + vn */;
  rp = t->_mp_d;
  up = op1->_mp_d;
  vp = op2->_mp_d;

  /*@ Assert
        exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq l1_neq l2_neq,
          rop == rop@pre &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size_neq, op2size_neq) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          un + vn <= INT_MAX &&
          un == Zabs(op1size_neq) &&
          vn == Zabs(op2size_neq) &&
          op1size_neq != 0 &&
          op2size_neq != 0 &&
          same_sign(z1_neq, op1size_neq) &&
          same_sign(z2_neq, op2size_neq) &&
          same_sign(old_neq, rsize_neq) &&
          Zabs(rsize_neq) <= rcap_neq &&
          Zlength(l1_neq) == un &&
          Zlength(l2_neq) == vn &&
          list_within_bound(UINT_MOD, l1_neq) &&
          list_within_bound(UINT_MOD, l2_neq) &&
          list_to_Z(UINT_MOD, l1_neq) == Zabs(z1_neq) &&
          list_to_Z(UINT_MOD, l2_neq) == Zabs(z2_neq) &&
          last(l1_neq, 1) >= 1 &&
          last(l2_neq, 1) >= 1 &&
          rop->_mp_size == rsize_neq &&
          rop->_mp_alloc == rcap_neq &&
          rop->_mp_d == rptr_neq &&
          up == op1ptr_neq &&
          vp == op2ptr_neq &&
          t->_mp_size == 0 &&
          t->_mp_alloc == un + vn &&
          t->_mp_d == rp &&
          mpd_store_Z_compact(UINT_MOD, rptr_neq, Zabs(old_neq), Zabs(rsize_neq)) *
          UIntArray::undef_seg(rptr_neq, Zabs(rsize_neq), rcap_neq) *
          store(&(op1->_mp_d), op1ptr_neq) *
          store(&(op1->_mp_size), op1size_neq) *
          store(&(op1->_mp_alloc), op1cap_neq) *
          UIntArray::full(op1ptr_neq, un, l1_neq) *
          UIntArray::undef_seg(op1ptr_neq, un, op1cap_neq) *
          store(&(op2->_mp_d), op2ptr_neq) *
          store(&(op2->_mp_size), op2size_neq) *
          store(&(op2->_mp_alloc), op2cap_neq) *
          UIntArray::full(op2ptr_neq, vn, l2_neq) *
          UIntArray::undef_seg(op2ptr_neq, vn, op2cap_neq) *
          has_permission(&high) *
          UIntArray::undef_full(rp, un + vn) $ neq */
  /*@ Assert
        exists rptr_r_eq_op1 rsize_r_eq_op1 rcap_r_eq_op1 op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 l1_r_eq_op1 l2_r_eq_op1,
          rop == rop@pre &&
          rop == op1 &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size_r_eq_op1, op2size_r_eq_op1) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          un + vn <= INT_MAX &&
          un == Zabs(op1size_r_eq_op1) &&
          vn == Zabs(op2size_r_eq_op1) &&
          op1size_r_eq_op1 != 0 &&
          op2size_r_eq_op1 != 0 &&
          same_sign(z1_r_eq_op1, op1size_r_eq_op1) &&
          same_sign(z2_r_eq_op1, op2size_r_eq_op1) &&
          rptr_r_eq_op1 == op1ptr_r_eq_op1 &&
          rsize_r_eq_op1 == op1size_r_eq_op1 &&
          rcap_r_eq_op1 == op1cap_r_eq_op1 &&
          Zabs(rsize_r_eq_op1) <= rcap_r_eq_op1 &&
          Zlength(l1_r_eq_op1) == un &&
          Zlength(l2_r_eq_op1) == vn &&
          list_within_bound(UINT_MOD, l1_r_eq_op1) &&
          list_within_bound(UINT_MOD, l2_r_eq_op1) &&
          list_to_Z(UINT_MOD, l1_r_eq_op1) == Zabs(z1_r_eq_op1) &&
          list_to_Z(UINT_MOD, l2_r_eq_op1) == Zabs(z2_r_eq_op1) &&
          last(l1_r_eq_op1, 1) >= 1 &&
          last(l2_r_eq_op1, 1) >= 1 &&
          up == op1ptr_r_eq_op1 &&
          vp == op2ptr_r_eq_op1 &&
          t->_mp_size == 0 &&
          t->_mp_alloc == un + vn &&
          t->_mp_d == rp &&
          store(&(op1->_mp_d), op1ptr_r_eq_op1) *
          store(&(op1->_mp_size), op1size_r_eq_op1) *
          store(&(op1->_mp_alloc), op1cap_r_eq_op1) *
          UIntArray::full(op1ptr_r_eq_op1, un, l1_r_eq_op1) *
          UIntArray::undef_seg(op1ptr_r_eq_op1, un, op1cap_r_eq_op1) *
          store(&(op2->_mp_d), op2ptr_r_eq_op1) *
          store(&(op2->_mp_size), op2size_r_eq_op1) *
          store(&(op2->_mp_alloc), op2cap_r_eq_op1) *
          UIntArray::full(op2ptr_r_eq_op1, vn, l2_r_eq_op1) *
          UIntArray::undef_seg(op2ptr_r_eq_op1, vn, op2cap_r_eq_op1) *
          has_permission(&high) *
          UIntArray::undef_full(rp, un + vn) $ r_eq_op1 */
  /*@ Assert
        exists rptr_r_eq_op2 rsize_r_eq_op2 rcap_r_eq_op2 op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 l1_r_eq_op2 l2_r_eq_op2,
          rop == rop@pre &&
          rop == op2 &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size_r_eq_op2, op2size_r_eq_op2) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          un + vn <= INT_MAX &&
          un == Zabs(op1size_r_eq_op2) &&
          vn == Zabs(op2size_r_eq_op2) &&
          op1size_r_eq_op2 != 0 &&
          op2size_r_eq_op2 != 0 &&
          same_sign(z1_r_eq_op2, op1size_r_eq_op2) &&
          same_sign(z2_r_eq_op2, op2size_r_eq_op2) &&
          rptr_r_eq_op2 == op2ptr_r_eq_op2 &&
          rsize_r_eq_op2 == op2size_r_eq_op2 &&
          rcap_r_eq_op2 == op2cap_r_eq_op2 &&
          Zabs(rsize_r_eq_op2) <= rcap_r_eq_op2 &&
          Zlength(l1_r_eq_op2) == un &&
          Zlength(l2_r_eq_op2) == vn &&
          list_within_bound(UINT_MOD, l1_r_eq_op2) &&
          list_within_bound(UINT_MOD, l2_r_eq_op2) &&
          list_to_Z(UINT_MOD, l1_r_eq_op2) == Zabs(z1_r_eq_op2) &&
          list_to_Z(UINT_MOD, l2_r_eq_op2) == Zabs(z2_r_eq_op2) &&
          last(l1_r_eq_op2, 1) >= 1 &&
          last(l2_r_eq_op2, 1) >= 1 &&
          up == op1ptr_r_eq_op2 &&
          vp == op2ptr_r_eq_op2 &&
          t->_mp_size == 0 &&
          t->_mp_alloc == un + vn &&
          t->_mp_d == rp &&
          store(&(op1->_mp_d), op1ptr_r_eq_op2) *
          store(&(op1->_mp_size), op1size_r_eq_op2) *
          store(&(op1->_mp_alloc), op1cap_r_eq_op2) *
          UIntArray::full(op1ptr_r_eq_op2, un, l1_r_eq_op2) *
          UIntArray::undef_seg(op1ptr_r_eq_op2, un, op1cap_r_eq_op2) *
          store(&(op2->_mp_d), op2ptr_r_eq_op2) *
          store(&(op2->_mp_size), op2size_r_eq_op2) *
          store(&(op2->_mp_alloc), op2cap_r_eq_op2) *
          UIntArray::full(op2ptr_r_eq_op2, vn, l2_r_eq_op2) *
          UIntArray::undef_seg(op2ptr_r_eq_op2, vn, op2cap_r_eq_op2) *
          has_permission(&high) *
          UIntArray::undef_full(rp, un + vn) $ r_eq_op2 */
  if (un >= vn) {
    /*@ Given rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq l1_neq l2_neq $ neq */
  /*@ Given rptr_r_eq_op1 rsize_r_eq_op1 rcap_r_eq_op1 op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 l1_r_eq_op1 l2_r_eq_op1 $ r_eq_op1 */
  /*@ Given rptr_r_eq_op2 rsize_r_eq_op2 rcap_r_eq_op2 op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 l1_r_eq_op2 l2_r_eq_op2 $ r_eq_op2 */
    mpn_mul(rp, up, un, vp, vn)
      /*@ where l_src = l1_neq, l_vp = l2_neq $ neq
        where l_src = l1_r_eq_op1, l_vp = l2_r_eq_op1 $ r_eq_op1
        where l_src = l1_r_eq_op2, l_vp = l2_r_eq_op2 $ r_eq_op2 */;
  } else {
    /*@ Assert
        exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq l1_neq l2_neq,
          rop == rop@pre &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un < vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size_neq, op2size_neq) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          vn + un <= INT_MAX &&
          un == Zabs(op1size_neq) &&
          vn == Zabs(op2size_neq) &&
          op1size_neq != 0 &&
          op2size_neq != 0 &&
          same_sign(z1_neq, op1size_neq) &&
          same_sign(z2_neq, op2size_neq) &&
          same_sign(old_neq, rsize_neq) &&
          Zabs(rsize_neq) <= rcap_neq &&
          Zlength(l1_neq) == un &&
          Zlength(l2_neq) == vn &&
          list_within_bound(UINT_MOD, l1_neq) &&
          list_within_bound(UINT_MOD, l2_neq) &&
          list_to_Z(UINT_MOD, l1_neq) == Zabs(z1_neq) &&
          list_to_Z(UINT_MOD, l2_neq) == Zabs(z2_neq) &&
          last(l1_neq, 1) >= 1 &&
          last(l2_neq, 1) >= 1 &&
          rop->_mp_size == rsize_neq &&
          rop->_mp_alloc == rcap_neq &&
          rop->_mp_d == rptr_neq &&
          up == op1ptr_neq &&
          vp == op2ptr_neq &&
          t->_mp_size == 0 &&
          t->_mp_alloc == un + vn &&
          t->_mp_d == rp &&
          mpd_store_Z_compact(UINT_MOD, rptr_neq, Zabs(old_neq), Zabs(rsize_neq)) *
          UIntArray::undef_seg(rptr_neq, Zabs(rsize_neq), rcap_neq) *
          store(&(op1->_mp_d), op1ptr_neq) *
          store(&(op1->_mp_size), op1size_neq) *
          store(&(op1->_mp_alloc), op1cap_neq) *
          UIntArray::full(up, un, l1_neq) *
          UIntArray::undef_seg(up, un, op1cap_neq) *
          store(&(op2->_mp_d), op2ptr_neq) *
          store(&(op2->_mp_size), op2size_neq) *
          store(&(op2->_mp_alloc), op2cap_neq) *
          UIntArray::full(vp, vn, l2_neq) *
          UIntArray::undef_seg(vp, vn, op2cap_neq) *
          has_permission(&high) *
          UIntArray::undef_full(rp, vn + un) $ neq */
  /*@ Assert
        exists rptr_r_eq_op1 rsize_r_eq_op1 rcap_r_eq_op1 op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 l1_r_eq_op1 l2_r_eq_op1,
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
          mpz_mul_sign(sign, op1size_r_eq_op1, op2size_r_eq_op1) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          vn + un <= INT_MAX &&
          un == Zabs(op1size_r_eq_op1) &&
          vn == Zabs(op2size_r_eq_op1) &&
          op1size_r_eq_op1 != 0 &&
          op2size_r_eq_op1 != 0 &&
          same_sign(z1_r_eq_op1, op1size_r_eq_op1) &&
          same_sign(z2_r_eq_op1, op2size_r_eq_op1) &&
          rptr_r_eq_op1 == op1ptr_r_eq_op1 &&
          rsize_r_eq_op1 == op1size_r_eq_op1 &&
          rcap_r_eq_op1 == op1cap_r_eq_op1 &&
          Zabs(rsize_r_eq_op1) <= rcap_r_eq_op1 &&
          Zlength(l1_r_eq_op1) == un &&
          Zlength(l2_r_eq_op1) == vn &&
          list_within_bound(UINT_MOD, l1_r_eq_op1) &&
          list_within_bound(UINT_MOD, l2_r_eq_op1) &&
          list_to_Z(UINT_MOD, l1_r_eq_op1) == Zabs(z1_r_eq_op1) &&
          list_to_Z(UINT_MOD, l2_r_eq_op1) == Zabs(z2_r_eq_op1) &&
          last(l1_r_eq_op1, 1) >= 1 &&
          last(l2_r_eq_op1, 1) >= 1 &&
          up == op1ptr_r_eq_op1 &&
          vp == op2ptr_r_eq_op1 &&
          t->_mp_size == 0 &&
          t->_mp_alloc == un + vn &&
          t->_mp_d == rp &&
          store(&(op1->_mp_d), op1ptr_r_eq_op1) *
          store(&(op1->_mp_size), op1size_r_eq_op1) *
          store(&(op1->_mp_alloc), op1cap_r_eq_op1) *
          UIntArray::full(up, un, l1_r_eq_op1) *
          UIntArray::undef_seg(up, un, op1cap_r_eq_op1) *
          store(&(op2->_mp_d), op2ptr_r_eq_op1) *
          store(&(op2->_mp_size), op2size_r_eq_op1) *
          store(&(op2->_mp_alloc), op2cap_r_eq_op1) *
          UIntArray::full(vp, vn, l2_r_eq_op1) *
          UIntArray::undef_seg(vp, vn, op2cap_r_eq_op1) *
          has_permission(&high) *
          UIntArray::undef_full(rp, vn + un) $ r_eq_op1 */
  /*@ Assert
        exists rptr_r_eq_op2 rsize_r_eq_op2 rcap_r_eq_op2 op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 l1_r_eq_op2 l2_r_eq_op2,
          rop == rop@pre &&
          rop == op2 &&
          op1 == op1@pre &&
          op2 == op2@pre &&
          rn == un + vn &&
          un < vn &&
          un > 0 &&
          vn > 0 &&
          0 <= sign &&
          sign <= 1 &&
          mpz_mul_sign(sign, op1size_r_eq_op2, op2size_r_eq_op2) &&
          un <= INT_MAX &&
          vn <= INT_MAX &&
          vn + un <= INT_MAX &&
          un == Zabs(op1size_r_eq_op2) &&
          vn == Zabs(op2size_r_eq_op2) &&
          op1size_r_eq_op2 != 0 &&
          op2size_r_eq_op2 != 0 &&
          same_sign(z1_r_eq_op2, op1size_r_eq_op2) &&
          same_sign(z2_r_eq_op2, op2size_r_eq_op2) &&
          rptr_r_eq_op2 == op2ptr_r_eq_op2 &&
          rsize_r_eq_op2 == op2size_r_eq_op2 &&
          rcap_r_eq_op2 == op2cap_r_eq_op2 &&
          Zabs(rsize_r_eq_op2) <= rcap_r_eq_op2 &&
          Zlength(l1_r_eq_op2) == un &&
          Zlength(l2_r_eq_op2) == vn &&
          list_within_bound(UINT_MOD, l1_r_eq_op2) &&
          list_within_bound(UINT_MOD, l2_r_eq_op2) &&
          list_to_Z(UINT_MOD, l1_r_eq_op2) == Zabs(z1_r_eq_op2) &&
          list_to_Z(UINT_MOD, l2_r_eq_op2) == Zabs(z2_r_eq_op2) &&
          last(l1_r_eq_op2, 1) >= 1 &&
          last(l2_r_eq_op2, 1) >= 1 &&
          up == op1ptr_r_eq_op2 &&
          vp == op2ptr_r_eq_op2 &&
          t->_mp_size == 0 &&
          t->_mp_alloc == un + vn &&
          t->_mp_d == rp &&
          store(&(op1->_mp_d), op1ptr_r_eq_op2) *
          store(&(op1->_mp_size), op1size_r_eq_op2) *
          store(&(op1->_mp_alloc), op1cap_r_eq_op2) *
          UIntArray::full(up, un, l1_r_eq_op2) *
          UIntArray::undef_seg(up, un, op1cap_r_eq_op2) *
          store(&(op2->_mp_d), op2ptr_r_eq_op2) *
          store(&(op2->_mp_size), op2size_r_eq_op2) *
          store(&(op2->_mp_alloc), op2cap_r_eq_op2) *
          UIntArray::full(vp, vn, l2_r_eq_op2) *
          UIntArray::undef_seg(vp, vn, op2cap_r_eq_op2) *
          has_permission(&high) *
          UIntArray::undef_full(rp, vn + un) $ r_eq_op2 */
    /*@ Given rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq l1_neq l2_neq $ neq */
  /*@ Given rptr_r_eq_op1 rsize_r_eq_op1 rcap_r_eq_op1 op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 l1_r_eq_op1 l2_r_eq_op1 $ r_eq_op1 */
  /*@ Given rptr_r_eq_op2 rsize_r_eq_op2 rcap_r_eq_op2 op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 l1_r_eq_op2 l2_r_eq_op2 $ r_eq_op2 */
    mpn_mul(rp, vp, vn, up, un)
      /*@ where l_src = l2_neq, l_vp = l1_neq $ neq
        where l_src = l2_r_eq_op1, l_vp = l1_r_eq_op1 $ r_eq_op1
        where l_src = l2_r_eq_op2, l_vp = l1_r_eq_op2 $ r_eq_op2 */;
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
        op1 == op1@pre &&
        op2 == op2@pre &&
        store_Z(rop, old_neq) *
        store_Z(op1, z1_neq) *
        store_Z(op2, z2_neq) *
        store_Z(t, z1_neq * z2_neq) *
        has_permission(&sign) *
        has_permission(&un) *
        has_permission(&vn) *
        has_permission(&rn) *
        has_permission(&rp) *
        has_permission(&up) *
        has_permission(&vp) *
        has_permission(&high) $ neq */
  /*@ Assert
        rop == rop@pre &&
        rop == op1 &&
        op1 == op1@pre &&
        op2 == op2@pre &&
        store_Z(op1, z1_r_eq_op1) *
        store_Z(op2, z2_r_eq_op1) *
        store_Z(t, z1_r_eq_op1 * z2_r_eq_op1) *
        has_permission(&sign) *
        has_permission(&un) *
        has_permission(&vn) *
        has_permission(&rn) *
        has_permission(&rp) *
        has_permission(&up) *
        has_permission(&vp) *
        has_permission(&high) $ r_eq_op1 */
  /*@ Assert
        rop == rop@pre &&
        rop == op2 &&
        op1 == op1@pre &&
        op2 == op2@pre &&
        store_Z(op1, z1_r_eq_op2) *
        store_Z(op2, z2_r_eq_op2) *
        store_Z(t, z1_r_eq_op2 * z2_r_eq_op2) *
        has_permission(&sign) *
        has_permission(&un) *
        has_permission(&vn) *
        has_permission(&rn) *
        has_permission(&rp) *
        has_permission(&up) *
        has_permission(&vp) *
        has_permission(&high) $ r_eq_op2 */
  mpz_swap(rop, t);
  mpz_clear(t);
  free_mpz_struct(t);
}
