#include "fme_ge_gmp/fme/fme_def.h"

struct InequList {
    mpz_ptr coef;
    struct InequList *next;
};

struct BoundPair {
    struct InequList *upper;
    struct InequList *lower;
    struct InequList *remain;
};

struct BoundPair *BP0;

struct InequList *malloc_InequList()
  /*@ Require emp
      Ensure __return != 0 &&
             undef_data_at(&(__return->coef)) *
             undef_data_at(&(__return->next))
    */;

mpz_ptr malloc_coef_array(int len)
  /*@ Require emp
	      Ensure exists l, __return != 0 &&
	                       coef_Zlength(l) == len &&
	                       mpz_coef_array(__return, len, l)
    */;

void free_list_cell(struct InequList *p)
  /*@ With p_coef p_next
      Require store(&(p->coef), p_coef) *
              store(&(p->next), p_next)
      Ensure emp
    */;

void free_coef_array(mpz_ptr c)
  /*@ With n c0
      Require mpz_coef_array(c, n, c0)
      Ensure emp
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

int mpz_sgn (const mpz_t u)
/*@
  With
    n
  Require
    store_Z(u, n)
  Ensure
    store_Z(u, n) &&
    (n > 0 && __return == 1 || n == 0 && __return == 0 ||
      n < 0 && __return == -1)
*/;

void mpz_set(mpz_ptr rop, mpz_srcptr op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure store_Z(rop, z) * store_Z(op, z)
*/;

void mpz_neg(mpz_ptr rop, mpz_srcptr op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure store_Z(rop, -z) * store_Z(op, z)
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
*/;

void mpz_divexact(mpz_ptr q, mpz_srcptr num, mpz_srcptr den)
/*@
  With
    old zn zd
  Require
    q != 0 &&
    zd != 0 &&
    zn == (zn / zd) * zd &&
    store_Z(q, old) * store_Z(num, zn) * store_Z(den, zd)
  Ensure
    store_Z(q, zn / zd) * store_Z(num, zn) * store_Z(den, zd)
*/;

void mpz_mul(mpz_ptr rop, mpz_srcptr op1, mpz_srcptr op2)
/*@
  With
    old z1 z2
  Require
    store_Z(rop, old) * store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    store_Z(rop, z1 * z2) * store_Z(op1, z1) * store_Z(op2, z2)
*/;

void mpz_addmul(mpz_ptr rop, mpz_srcptr op1, mpz_srcptr op2)
/*@
  With
    old z1 z2
  Require
    store_Z(rop, old) * store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    store_Z(rop, old + z1 * z2) * store_Z(op1, z1) * store_Z(op2, z2)
*/;

struct InequList *NilInequList()
  /*@ Require emp
      Ensure __return == 0 && emp
    */
{
    return (void *)0;
}

struct InequList *ConsInequList(mpz_ptr c, struct InequList *l)
  /*@ With n c0 l0
      Require c != 0 && mpz_coef_array(c, n, c0) * InequList(l, n, l0)
      Ensure __return != 0 && InequList(__return, n, cons(c0, l0))
    */
{
    struct InequList *res = malloc_InequList();
    res->coef = c;
    res->next = l;
    return res;
}

void free_InequList(struct InequList *p)
  /*@ With n l
      Require InequList(p, n, l)
      Ensure emp
    */
{
    if (p == (void *)0) {
        return;
    }
    if (p->coef != (void *)0) {
        free_coef_array(p->coef);
    }
    if (p->next != (void *)0) {
        free_InequList(p->next);
    }
    free_list_cell(p);
}

void eliminate(struct InequList *r, int num)
  /*@ high_level_spec <= low_level_spec
      With n l
      Require 1 <= num &&
              num < n &&
              BP0 != 0 &&
              undef_data_at(&(BP0->upper)) *
              undef_data_at(&(BP0->lower)) *
              undef_data_at(&(BP0->remain)) *
              InequList(r, n, l)
      Ensure exists b up lo re,
                    eliminate_xn(num, l, b) &&
                    form_BP(up, lo, re, b) &&
                    InequList_nth_pos(num, up) &&
                    InequList_nth_neg(num, lo) &&
                    BP0 == BP0@pre &&
                    InequList(BP0->upper, n, up) *
                    InequList(BP0->lower, n, lo) *
                    InequList(BP0->remain, n, re)
    */;

void eliminate(struct InequList *r, int num)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} n l (c: BP -> program unit B) X
      Require safeExec(ATrue, bind(eliminate_prog(num, l), c), X) &&
              1 <= num &&
              num < n &&
              BP0 != 0 &&
              undef_data_at(&(BP0->upper)) *
              undef_data_at(&(BP0->lower)) *
              undef_data_at(&(BP0->remain)) *
              InequList(r, n, l)
      Ensure exists b up lo re,
                    safeExec(ATrue, applyf(c, b), X) &&
                    form_BP(up, lo, re, b) &&
                    BP0 == BP0@pre &&
                    InequList(BP0->upper, n, up) *
                    InequList(BP0->lower, n, lo) *
                    InequList(BP0->remain, n, re)
    */;

void eliminate(struct InequList *r, int num)
  /*@ low_level_spec_aux_with_rel <= low_level_spec
      With {B} n l (c: BP -> program unit B) X
      Require safeExec(ATrue, bind(eliminate_prog(num, l), c), X) &&
              1 <= num &&
              num < n &&
              BP0 != 0 &&
              undef_data_at(&(BP0->upper)) *
              undef_data_at(&(BP0->lower)) *
              undef_data_at(&(BP0->remain)) *
              InequList(r, n, l)
      Ensure exists b up lo re,
                    safeExec(ATrue, applyf(c, b), X) &&
                    eliminate_xn(num, l, b) &&
                    form_BP(up, lo, re, b) &&
                    BP0 == BP0@pre &&
                    InequList(BP0->upper, n, up) *
                    InequList(BP0->lower, n, lo) *
                    InequList(BP0->remain, n, re)
    */;

void eliminate(struct InequList *r, int num)
  /*@ low_level_spec
      With n l X
      Require safeExec(ATrue, eliminate_prog(num, l), X) &&
              1 <= num &&
              num < n &&
              BP0 != 0 &&
              undef_data_at(&(BP0->upper)) *
              undef_data_at(&(BP0->lower)) *
              undef_data_at(&(BP0->remain)) *
              InequList(r, n, l)
      Ensure exists b up lo re,
                    safeExec(ATrue, return(b), X) &&
                    form_BP(up, lo, re, b) &&
                    BP0 == BP0@pre &&
                    InequList(BP0->upper, n, up) *
                    InequList(BP0->lower, n, lo) *
                    InequList(BP0->remain, n, re)
    */
{
    struct InequList *upper = NilInequList();
    struct InequList *lower = NilInequList();
    struct InequList *remain = NilInequList();
    struct InequList *cur = r;
    struct InequList *cur_next;

    /*@ Inv Assert
          exists up lo re todo b,
            safeExec(ATrue, eliminate_from(num, todo, b), X) &&
            form_BP(up, lo, re, b) &&
            num == num@pre &&
            r == r@pre &&
            BP0 == BP0@pre &&
            1 <= num &&
            num < n &&
            has_permission(&cur_next) *
            has_permission(&(BP0->upper)) *
            has_permission(&(BP0->lower)) *
            has_permission(&(BP0->remain)) *
            InequList(upper, n, up) *
            InequList(lower, n, lo) *
            InequList(remain, n, re) *
            InequList(cur, n, todo)
    */
    while (cur != (void *)0) {
        int sign;

        cur_next = cur->next;
        sign = mpz_sgn(cur->coef + num);
        if (sign != 0) {
            if (sign > 0) {
                cur->next = upper;
                upper = cur;
            } else {
                cur->next = lower;
                lower = cur;
            }
        } else {
            cur->next = remain;
            remain = cur;
        }
        cur = cur_next;
    }

    BP0->upper = upper;
    BP0->lower = lower;
    BP0->remain = remain;
}

mpz_ptr generate_new_constr(mpz_srcptr r1,
                            mpz_srcptr r2,
                            int num,
                            int cur_num)
  /*@ high_level_spec <= low_level_spec
      With c1 c2
      Require 1 <= cur_num &&
              cur_num < num + 1 &&
              num <= INT_MAX - 1 &&
              r1 != 0 && r2 != 0 &&
              coef_Znth(cur_num, c1, 0) > 0 &&
              coef_Znth(cur_num, c2, 0) < 0 &&
              mpz_coef_array(r1, num + 1, c1) *
              mpz_coef_array(r2, num + 1, c2)
      Ensure exists c3,
              __return != 0 &&
              generate_new_constraint(cur_num, c1, c2, c3) &&
              mpz_coef_array(r1, num + 1, c1) *
              mpz_coef_array(r2, num + 1, c2) *
              mpz_coef_array(__return, num + 1, c3)
    */;

mpz_ptr generate_new_constr(mpz_srcptr r1,
                            mpz_srcptr r2,
                            int num,
                            int cur_num)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} c1 c2 (c: Constraint -> program unit B) X
      Require safeExec(ATrue, bind(generate_new_constr_prog(cur_num, c1, c2), c), X) &&
              1 <= cur_num &&
              cur_num < num + 1 &&
              num <= INT_MAX - 1 &&
              r1 != 0 && r2 != 0 &&
              mpz_coef_array(r1, num + 1, c1) *
              mpz_coef_array(r2, num + 1, c2)
      Ensure exists c3,
              __return != 0 &&
              safeExec(ATrue, applyf(c, c3), X) &&
              mpz_coef_array(r1, num + 1, c1) *
              mpz_coef_array(r2, num + 1, c2) *
              mpz_coef_array(__return, num + 1, c3)
    */;

mpz_ptr generate_new_constr(mpz_srcptr r1,
                            mpz_srcptr r2,
                            int num,
                            int cur_num)
  /*@ low_level_spec
      With c1 c2 X
      Require safeExec(ATrue, generate_new_constr_prog(cur_num, c1, c2), X) &&
              1 <= cur_num &&
              cur_num < num + 1 &&
              num <= INT_MAX - 1 &&
              r1 != 0 && r2 != 0 &&
              mpz_coef_array(r1, num + 1, c1) *
              mpz_coef_array(r2, num + 1, c2)
      Ensure exists c3,
              __return != 0 &&
              safeExec(ATrue, return(c3), X) &&
              mpz_coef_array(r1, num + 1, c1) *
              mpz_coef_array(r2, num + 1, c2) *
              mpz_coef_array(__return, num + 1, c3)
    */
{
    mpz_ptr an;
    mpz_ptr bn;
    mpz_ptr gcd_val;
    mpz_ptr m1;
    mpz_ptr m2;
    mpz_ptr tmp;
    mpz_ptr res;
    int i;

    an = malloc_mpz_struct();
    bn = malloc_mpz_struct();
    gcd_val = malloc_mpz_struct();
    m1 = malloc_mpz_struct();
    m2 = malloc_mpz_struct();
    tmp = malloc_mpz_struct();

    mpz_init(an);
    mpz_init(bn);
    mpz_init(gcd_val);
    mpz_init(m1);
    mpz_init(m2);
    mpz_init(tmp);

    mpz_set(an, r1 + cur_num) /*@ where (neq) */;
    mpz_neg(bn, r2 + cur_num) /*@ where (neq) */;
    mpz_gcd(gcd_val, an, bn);
    mpz_divexact(m1, bn, gcd_val)
      /*@ where old = 0,
          zn = -coef_Znth(cur_num, c2, 0),
          zd = Zgcd(coef_Znth(cur_num, c1, 0),
                    -coef_Znth(cur_num, c2, 0)) */;
    mpz_divexact(m2, an, gcd_val)
      /*@ where old = 0,
          zn = coef_Znth(cur_num, c1, 0),
          zd = Zgcd(coef_Znth(cur_num, c1, 0),
                    -coef_Znth(cur_num, c2, 0)) */;

    res = malloc_coef_array(num + 1);
    /*@ Inv Assert
          exists c3 prefix an_v bn_v g_v m1_v m2_v tmp_v,
            safeExec(ATrue, generate_new_constr_from(m1_v, m2_v, c1, c2, i, prefix), X) &&
            r1 == r1@pre &&
            r2 == r2@pre &&
            num == num@pre &&
            cur_num == cur_num@pre &&
            an_v == coef_Znth(cur_num, c1, 0) &&
            bn_v == -coef_Znth(cur_num, c2, 0) &&
            g_v == Zgcd(an_v, bn_v) &&
            m1_v == bn_v / g_v &&
            m2_v == an_v / g_v &&
            0 <= i &&
            i <= num + 1 &&
            i == Zlength(prefix) &&
            1 <= cur_num &&
            cur_num < num + 1 &&
            num <= INT_MAX - 1 &&
            r1 != 0 &&
            r2 != 0 &&
            res != 0 &&
            coef_Zlength(c1) == num + 1 &&
            coef_Zlength(c2) == num + 1 &&
            coef_Zlength(c3) == num + 1 &&
            coef_pre_eq(i, c3, list_Constraint(prefix)) &&
            store_Z(an, an_v) *
            store_Z(bn, bn_v) *
            store_Z(gcd_val, g_v) *
            store_Z(m1, m1_v) *
            store_Z(m2, m2_v) *
            store_Z(tmp, tmp_v) *
            mpz_coef_array(r1, num + 1, c1) *
            mpz_coef_array(r2, num + 1, c2) *
            mpz_coef_array(res, num + 1, c3)
    */
    for (i = 0; i <= num; i++) {
        mpz_mul(tmp, m1, r1 + i);
        mpz_addmul(tmp, m2, r2 + i);
        mpz_set(res + i, tmp) /*@ where (neq) */;
    }

    mpz_clear(an);
    free_mpz_struct(an);
    mpz_clear(bn);
    free_mpz_struct(bn);
    mpz_clear(gcd_val);
    free_mpz_struct(gcd_val);
    mpz_clear(m1);
    free_mpz_struct(m1);
    mpz_clear(m2);
    free_mpz_struct(m2);
    mpz_clear(tmp);
    free_mpz_struct(tmp);

    return res;
}

struct InequList *generate_new_constraint_list(struct InequList *r1,
                                               struct InequList *r2,
                                               int num,
                                               int cur_num,
                                               struct InequList *init)
  /*@ high_level_spec <= low_level_spec
      With n l1 l2 l_init
      Require n == num + 1 &&
              1 <= cur_num &&
              cur_num < n &&
              num <= INT_MAX - 1 &&
              InequList_nth_pos(cur_num, l1) &&
              InequList_nth_neg(cur_num, l2) &&
              InequList(r1, n, l1) *
              InequList(r2, n, l2) *
              InequList(init, n, l_init)
      Ensure exists l3 l4,
              generate_new_constraints(cur_num, l1, l2, l4) &&
              l3 == app(l4, l_init) &&
              InequList(r1, n, l1) *
              InequList(r2, n, l2) *
              InequList(__return, n, l3)
    */;

struct InequList *generate_new_constraint_list(struct InequList *r1,
                                               struct InequList *r2,
                                               int num,
                                               int cur_num,
                                               struct InequList *init)
  /*@ low_level_spec_aux_with_rel <= low_level_spec
      With {B} n l1 l2 l_init (c: list Constraint -> program unit B) X
      Require safeExec(ATrue, bind(generate_new_constraint_list_prog(cur_num, l1, l2, l_init), c), X) &&
              n == num + 1 &&
              1 <= cur_num &&
              cur_num < n &&
              num <= INT_MAX - 1 &&
              InequList_nth_pos(cur_num, l1) &&
              InequList_nth_neg(cur_num, l2) &&
              InequList(r1, n, l1) *
              InequList(r2, n, l2) *
              InequList(init, n, l_init)
      Ensure exists l3 l4,
              safeExec(ATrue, applyf(c, l3), X) &&
              generate_new_constraints(cur_num, l1, l2, l4) &&
              l3 == app(l4, l_init) &&
              InequList(r1, n, l1) *
              InequList(r2, n, l2) *
              InequList(__return, n, l3)
    */;

struct InequList *generate_new_constraint_list(struct InequList *r1,
                                               struct InequList *r2,
                                               int num,
                                               int cur_num,
                                               struct InequList *init)
  /*@ low_level_spec
      With n l1 l2 l_init X
      Require safeExec(ATrue, generate_new_constraint_list_prog(cur_num, l1, l2, l_init), X) &&
              n == num + 1 &&
              1 <= cur_num &&
              cur_num < n &&
              num <= INT_MAX - 1 &&
              InequList(r1, n, l1) *
              InequList(r2, n, l2) *
              InequList(init, n, l_init)
      Ensure exists l3,
              safeExec(ATrue, return(l3), X) &&
              InequList(r1, n, l1) *
              InequList(r2, n, l2) *
              InequList(__return, n, l3)
    */
{
    struct InequList *res = init;
    struct InequList *p1 = r1;

    /*@ Inv Assert
          exists l11 l12 acc,
            safeExec(ATrue, generate_new_constraint_list_loop(cur_num, l12, l2, acc), X) &&
            l1 == app(l11, l12) &&
            r1 == r1@pre &&
            r2 == r2@pre &&
            init == init@pre &&
            num == num@pre &&
            cur_num == cur_num@pre &&
            n == num + 1 &&
            1 <= cur_num &&
            cur_num < n &&
            num <= INT_MAX - 1 &&
            InequList_seg(r1, p1, n, l11) *
            InequList(p1, n, l12) *
            InequList(r2, n, l2) *
            InequList(res, n, acc)
    */
    while (p1 != (void *)0) {
        struct InequList *p2 = r2;
        /*@ Inv Assert
              exists l11 l12 l12_tail c1_cur l21 l22 acc,
                safeExec(ATrue,
                  bind(generate_new_constraints_inner_loop(cur_num, c1_cur, l22, acc),
                       generate_new_constraint_list_loop(cur_num, l12_tail, l2)), X) &&
                l1 == app(l11, l12) &&
                l12 == cons(c1_cur, l12_tail) &&
                l2 == app(l21, l22) &&
                p1 != 0 &&
                r1 == r1@pre &&
                r2 == r2@pre &&
                init == init@pre &&
                num == num@pre &&
                cur_num == cur_num@pre &&
                n == num + 1 &&
                1 <= cur_num &&
                cur_num < n &&
                num <= INT_MAX - 1 &&
                InequList_seg(r1, p1, n, l11) *
                InequList(p1, n, l12) *
                InequList_seg(r2, p2, n, l21) *
                InequList(p2, n, l22) *
                InequList(res, n, acc)
        */
        while (p2 != (void *)0) {
            /*@ Assert
                  exists l11 l12 l12_tail c1_cur l21 l22 l22_tail c2_cur acc,
                    safeExec(ATrue,
                      bind(generate_new_constr_prog(cur_num, c1_cur, c2_cur),
                           generate_new_constraints_after_one(cur_num, c1_cur, l22_tail, acc, l12_tail, l2)), X) &&
                    l1 == app(l11, l12) &&
                    l12 == cons(c1_cur, l12_tail) &&
                    l2 == app(l21, l22) &&
                    l22 == cons(c2_cur, l22_tail) &&
                    p1 != 0 &&
                    p2 != 0 &&
                    p1->coef != 0 &&
                    p2->coef != 0 &&
                    r1 == r1@pre &&
                    r2 == r2@pre &&
                    init == init@pre &&
                    num == num@pre &&
                    cur_num == cur_num@pre &&
                    n == num + 1 &&
                    1 <= cur_num &&
                    cur_num < n &&
                    num <= INT_MAX - 1 &&
                    InequList_seg(r1, p1, n, l11) *
                    mpz_coef_array(p1->coef, n, c1_cur) *
                    InequList(p1->next, n, l12_tail) *
                    InequList_seg(r2, p2, n, l21) *
                    mpz_coef_array(p2->coef, n, c2_cur) *
                    InequList(p2->next, n, l22_tail) *
                    InequList(res, n, acc)
            */
            mpz_ptr tmp = generate_new_constr(p1->coef, p2->coef, num, cur_num) /*@ where(low_level_spec_aux) X = X; B = (list Constraint) */;
            res = ConsInequList(tmp, res);
            p2 = p2->next;
        }
        p1 = p1->next;
    }
    return res;
}

void real_shadow(struct InequList **pr, int n)
  /*@ high_level_spec <= low_level_spec
      With p1 l1
      Require BP0 != 0 && pr != 0 &&
              n >= 1 && n <= INT_MAX && n <= INT_MAX - 1 &&
              BP0->upper == 0 &&
              BP0->lower == 0 &&
              BP0->remain == 0 &&
              store(pr, p1) *
              InequList(p1, n + 1, l1)
      Ensure exists p2 l2,
              LP_implies(l1, l2) &&
              InequList_Zeros(l2, 1, n + 1) &&
              BP0 == BP0@pre &&
              store(pr, p2) *
              InequList(p2, n + 1, l2) *
              undef_data_at(&(BP0->upper)) *
              undef_data_at(&(BP0->lower)) *
              undef_data_at(&(BP0->remain))
    */;

void real_shadow(struct InequList **pr, int n)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} p1 l1 (c: list Constraint -> program unit B) X
      Require safeExec(ATrue, bind(real_shadow_prog(n, l1), c), X) &&
              BP0 != 0 && pr != 0 &&
              n >= 1 && n <= INT_MAX && n <= INT_MAX - 1 &&
              BP0->upper == 0 &&
              BP0->lower == 0 &&
              BP0->remain == 0 &&
              store(pr, p1) *
              InequList(p1, n + 1, l1)
      Ensure exists p2 l2,
              safeExec(ATrue, applyf(c, l2), X) &&
              BP0 == BP0@pre &&
              store(pr, p2) *
              InequList(p2, n + 1, l2) *
              undef_data_at(&(BP0->upper)) *
              undef_data_at(&(BP0->lower)) *
              undef_data_at(&(BP0->remain))
    */;

void real_shadow(struct InequList **pr, int n)
  /*@ low_level_spec
      With p1 l1 X
      Require safeExec(ATrue, real_shadow_prog(n, l1), X) &&
              BP0 != 0 && pr != 0 &&
              n >= 1 && n <= INT_MAX && n <= INT_MAX - 1 &&
              BP0->upper == 0 &&
              BP0->lower == 0 &&
              BP0->remain == 0 &&
              store(pr, p1) *
              InequList(p1, n + 1, l1)
      Ensure exists p2 l2,
              safeExec(ATrue, return(l2), X) &&
              BP0 == BP0@pre &&
              store(pr, p2) *
              InequList(p2, n + 1, l2) *
              undef_data_at(&(BP0->upper)) *
              undef_data_at(&(BP0->lower)) *
              undef_data_at(&(BP0->remain))
    */
{
    struct InequList *r = *pr;
    int cnt = n;

    /*@ Inv Assert
          exists l,
            safeExec(ATrue, real_shadow_loop_prog(cnt, l), X) &&
            BP0 == BP0@pre &&
            pr == pr@pre &&
            n == n@pre &&
            0 <= cnt &&
            cnt <= n &&
            n >= 1 &&
            n <= INT_MAX &&
            n <= INT_MAX - 1 &&
            BP0 != 0 &&
            pr != 0 &&
            store(pr, p1) *
            undef_data_at(&(BP0->upper)) *
            undef_data_at(&(BP0->lower)) *
            undef_data_at(&(BP0->remain)) *
            InequList(r, n + 1, l)
    */
    while (cnt >= 1) {
        eliminate(r, cnt) /*@ where(low_level_spec_aux_with_rel) c = real_shadow_after_eliminate(cnt), X = X; B = (list Constraint) */;
        if (BP0->remain == (void *)0 && BP0->upper == (void *)0) {
            free_InequList(BP0->lower);
            *pr = (void *)0;
            return;
        }
        if (BP0->remain == (void *)0 && BP0->lower == (void *)0) {
            free_InequList(BP0->upper);
            *pr = (void *)0;
            return;
        }

        r = generate_new_constraint_list(BP0->upper, BP0->lower, n, cnt, BP0->remain) /*@ where(low_level_spec_aux_with_rel) c = real_shadow_after_generate(cnt), X = X; B = (list Constraint) */;
        free_InequList(BP0->upper);
        free_InequList(BP0->lower);
        cnt--;
    }

    *pr = r;
}

int lia_deduction(struct InequList **pr, int n)
  /*@ high_level_spec <= low_level_spec
      With p1 l1
      Require BP0 != 0 && pr != 0 &&
              n >= 1 && n <= INT_MAX - 1 &&
              BP0->upper == 0 &&
              BP0->lower == 0 &&
              BP0->remain == 0 &&
              store(pr, p1) *
              InequList(p1, n + 1, l1)
      Ensure ((exists p2, __return == 1 &&
                  UNSAT(l1) &&
                  store(pr, p2) *
                  undef_data_at(&(BP0->upper)) *
                  undef_data_at(&(BP0->lower)) *
                  undef_data_at(&(BP0->remain)))
              ||
              (exists p2 l2, __return == 0 &&
                  LP_implies(l1, l2) &&
                  InequList_Zeros(l2, 1, n + 1) &&
                  store(pr, p2) *
                  InequList(p2, n + 1, l2) *
                  undef_data_at(&(BP0->upper)) *
                  undef_data_at(&(BP0->lower)) *
                  undef_data_at(&(BP0->remain))))
    */;

int lia_deduction(struct InequList **pr, int n)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} p1 l1 (c: (Z * (list Constraint)) -> program unit B) X
      Require safeExec(ATrue, bind(lia_deduction_prog(n, l1), c), X) &&
              BP0 != 0 && pr != 0 &&
              n >= 1 && n <= INT_MAX - 1 &&
              BP0->upper == 0 &&
              BP0->lower == 0 &&
              BP0->remain == 0 &&
              store(pr, p1) *
              InequList(p1, n + 1, l1)
      Ensure ((exists p2 l2, __return == 1 &&
                  safeExec(ATrue, applyf(c, makepair(1, l2)), X) &&
                  BP0 == BP0@pre &&
                  store(pr, p2) *
                  undef_data_at(&(BP0->upper)) *
                  undef_data_at(&(BP0->lower)) *
                  undef_data_at(&(BP0->remain)))
              ||
              (exists p2 l2, __return == 0 &&
                  safeExec(ATrue, applyf(c, makepair(0, l2)), X) &&
                  BP0 == BP0@pre &&
                  store(pr, p2) *
                  InequList(p2, n + 1, l2) *
                  undef_data_at(&(BP0->upper)) *
                  undef_data_at(&(BP0->lower)) *
                  undef_data_at(&(BP0->remain))))
    */;

int lia_deduction(struct InequList **pr, int n)
  /*@ low_level_spec
      With p1 l1 X
      Require safeExec(ATrue, lia_deduction_prog(n, l1), X) &&
              BP0 != 0 && pr != 0 &&
              n >= 1 && n <= INT_MAX - 1 &&
              BP0->upper == 0 &&
              BP0->lower == 0 &&
              BP0->remain == 0 &&
              store(pr, p1) *
              InequList(p1, n + 1, l1)
      Ensure ((exists p2 l2, __return == 1 &&
                  safeExec(ATrue, return(makepair(1, l2)), X) &&
                  BP0 == BP0@pre &&
                  store(pr, p2) *
                  undef_data_at(&(BP0->upper)) *
                  undef_data_at(&(BP0->lower)) *
                  undef_data_at(&(BP0->remain)))
              ||
              (exists p2 l2, __return == 0 &&
                  safeExec(ATrue, return(makepair(0, l2)), X) &&
                  BP0 == BP0@pre &&
                  store(pr, p2) *
                  InequList(p2, n + 1, l2) *
                  undef_data_at(&(BP0->upper)) *
                  undef_data_at(&(BP0->lower)) *
                  undef_data_at(&(BP0->remain))))
    */
{
    struct InequList *p;

    real_shadow(pr, n) /*@ where(low_level_spec_aux) c = lia_deduction_after_real_shadow, X = X; B = (Z * (list Constraint)) */;
    p = *pr;
    /*@ Inv Assert
          exists l_done l_todo l2 p2,
            safeExec(ATrue, lia_deduction_scan_from_false(l2, l_todo), X) &&
            l2 == app(l_done, l_todo) &&
            BP0 == BP0@pre &&
            pr == pr@pre &&
            n == n@pre &&
            BP0 != 0 &&
            pr != 0 &&
            n >= 1 &&
            n <= INT_MAX - 1 &&
            store(pr, p2) *
            undef_data_at(&(BP0->upper)) *
            undef_data_at(&(BP0->lower)) *
            undef_data_at(&(BP0->remain)) *
            InequList_seg(p2, p, n + 1, l_done) *
            InequList(p, n + 1, l_todo)
    */
    while (p != (void *)0) {
        if (mpz_sgn(p->coef) > 0) {
            /*@ Assert
                  exists l2 p2,
                    safeExec(ATrue, return(makepair(1, l2)), X) &&
                    BP0 == BP0@pre &&
                    pr == pr@pre &&
                    n == n@pre &&
                    p != 0 &&
                    BP0 != 0 &&
                    pr != 0 &&
                    n >= 1 &&
                    n <= INT_MAX - 1 &&
                    store(pr, p2) *
                    undef_data_at(&(BP0->upper)) *
                    undef_data_at(&(BP0->lower)) *
                    undef_data_at(&(BP0->remain)) *
                    InequList(p2, n + 1, l2)
            */
            free_InequList(*pr);
            return 1;
        }
        p = p->next;
    }
    return 0;
}
