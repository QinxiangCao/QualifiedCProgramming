


#include "mini-gmp.h"

int gmp_abs(int x)
/*@ default */
{
  return x >= 0 ? x : -x;
}

int gmp_max(int a, int b)
/*@ default */
{
  return a > b ? a : b;
}

int gmp_cmp(int a, int b)
/*@ default */
{
  return (a > b) - (a < b);
}

/* MPN interface */

/* 从 低地址向高地址 顺序复制 */
void
mpn_copyi (unsigned int *d, unsigned int *s, int n)
/*@ default */
{
  /*@
    mpd_store_Z(UINT_MOD, s, val, n)
    which implies
    exists l,
      Zlength(l) == n && 
      list_to_Z(UINT_MOD, l) == val && list_within_bound(UINT_MOD, l) &&
      UIntArray::full(s, n, l)
  */
  /*@ Given l */
  int i;
  /*@ Inv
    0 <= i && i <= n@pre && 
    UIntArray::full(d@pre, i, sublist(0, i, l)) * 
    UIntArray::undef_seg(d@pre, i, n@pre)
  */
  for (i = 0; i < n; i++) {
      d[i] = s[i];
  }
}

/* 大于返回1，小于返回-1，等于返回0 */
int
mpn_cmp (unsigned int *ap, unsigned int *bp, int n)
/*@ default */
{
  /*@
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) * mpd_store_Z_compact(UINT_MOD, bp, val2, n)
    which implies
    exists l1 l2,
    list_to_Z(UINT_MOD, l1) == val1 && last(l1, 1) >= 1 && list_within_bound(UINT_MOD, l1) &&
    list_to_Z(UINT_MOD, l2) == val2 && last(l2, 1) >= 1 && list_within_bound(UINT_MOD, l2) &&
    n == Zlength(l1) && n == Zlength(l2) && 
    UIntArray::full(ap, n, l1) * UIntArray::full(bp, n, l2) 
  */
  /*@
    Given l1 l2
  */
  --n;
  /*@ Inv
    -1 <= n && n < n@pre &&
    sublist(n + 1, n@pre, l1) == sublist(n + 1, n@pre, l2)
  */
  while (n >= 0)
    {
      if (ap[n] != bp[n])
	      return ap[n] > bp[n] ? 1 : -1;
      --n;
    }
  // Note: The parser cannot parse "--n" in loop condition so we paraphrased it.
  /*
  while (--n >= 0)
    {
      if (ap[n] != bp[n])
	return ap[n] > bp[n] ? 1 : -1;
    }
  */
  return 0;
}

/*处理位数不同的情况*/
static int
mpn_cmp4 (unsigned int *ap, int an, unsigned int *bp, int bn)
/*@ default */
{
  if (an != bn)
    return an < bn ? -1 : 1;
  else {
    return mpn_cmp (ap, bp, an);
  }
}


/*返回非0的位数*/
static int
mpn_normalized_size (unsigned int *xp, int n)
/*@ default */
{
  /*@
    mpd_store_Z(UINT_MOD, xp, val, n)
    which implies
    exists l,
    list_to_Z(UINT_MOD, l) == val && list_within_bound(UINT_MOD, l) && 
    Zlength(l) == n &&
    UIntArray::full(xp, n, l)
  */
  /*@ n <= INT_MAX by local */
  /*@
    Given l
  */
  /*@Inv
    n >= 0 && n <= n@pre &&
    list_to_Z(UINT_MOD, sublist(0, n, l)) == val &&
    UIntArray::full(xp@pre, n, sublist(0, n, l)) *
    UIntArray::undef_seg(xp@pre, n, n@pre)
  */
  while (n > 0 && xp[n-1] == 0)
    --n;
  return n;
}

/* 多精度数ap 加上单精度数b，返回最后产生的进位 */
unsigned int
mpn_add_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
/*@ default */
{
  /*@
    mpd_store_Z(UINT_MOD,ap, val, n)
    which implies
    exists l,
      Zlength(l) == n && 
      list_to_Z(UINT_MOD, l) == val && list_within_bound(UINT_MOD, l) &&
      UIntArray::full(ap, n, l)
  */

  /*@ Given l */
  int i;
  i = 0;
  do
  {
    unsigned int r = ap[i] + b;
    // Carry out
    b = (r < b);
    rp[i] = r;
    ++i;
  }
  /*@ Inv Assert 
    exists l' val1 val2,
    1 <= i && i <= n@pre && 0 <= b && b < UINT_MOD && n == n@pre &&
    ap == ap@pre && rp == rp@pre &&
    (val2 + b * Z::pow(UINT_MOD, i) == val1 + b@pre) &&
    Zlength(l') == i &&
    list_to_Z(UINT_MOD, sublist(0, i, l)) == val1 &&
    list_to_Z(UINT_MOD, l') == val2 &&
    list_within_bound(UINT_MOD, l') &&
    Zlength(l) == n && 
    list_to_Z(UINT_MOD, l) == val && list_within_bound(UINT_MOD, l) &&
    UIntArray::full(ap, n@pre, l) * 
    UIntArray::full(rp@pre, i, l') *
    UIntArray::undef_seg(rp@pre, i, n@pre)
  */
  while (i < n);

  return b;
}

/* 位数相同的多精度数ap 加上多精度数bp，返回最后产生的进位 */
unsigned int
mpn_add_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
/*@ implementation
 With val_a val_b
 Require
   n >= 0 &&
   mpd_store_Z(UINT_MOD, ap, val_a, n) *
   mpd_store_Z(UINT_MOD, bp, val_b, n) *
   UIntArray::undef_full(rp, n) 
 Ensure
   exists val_r_out,
   (val_r_out + __return * Z::pow(UINT_MOD, n) == val_a + val_b) &&
   mpd_store_Z(UINT_MOD, ap, val_a, n) *
   mpd_store_Z(UINT_MOD, bp, val_b, n) *
   mpd_store_Z(UINT_MOD, rp, val_r_out, n) 
*/
{
  /*@
    mpd_store_Z(UINT_MOD, ap, val_a, n) * mpd_store_Z(UINT_MOD, bp, val_b, n)
    which implies
    exists l_a l_b,
      Zlength(l_a) == n && Zlength(l_b) == n && 
      list_to_Z(UINT_MOD, l_a) == val_a && list_within_bound(UINT_MOD, l_a) &&
      list_to_Z(UINT_MOD, l_b) == val_b && list_within_bound(UINT_MOD, l_b) &&
      UIntArray::full(ap, n, l_a) * UIntArray::full(bp, n, l_b)
  */
  int i;
  unsigned int cy;

  i = 0;
  cy = 0;
  /*@ Given l_a l_b */

  /*@Inv
    exists l_r val_a_prefix val_b_prefix val_r,
      0 <= i && i <= n@pre && 0 <= cy && cy <= UINT_MAX &&
      list_to_Z(UINT_MOD, sublist(0, i, l_a)) == val_a_prefix &&
      list_to_Z(UINT_MOD, sublist(0, i, l_b)) == val_b_prefix &&
      list_to_Z(UINT_MOD, l_r) == val_r &&
      list_within_bound(UINT_MOD, l_r) &&
      Zlength(l_r) == i &&
      (val_r + cy * Z::pow(UINT_MOD, i) == val_a_prefix + val_b_prefix) &&
      UIntArray::full(rp@pre, i, l_r) *
      UIntArray::undef_seg(rp@pre, i, n@pre)
  */
  while (i < n)
  {
    unsigned int a, b, r;
    a = ap[i]; b = bp[i];
    r = a + cy;
    cy = (r < cy);
    r += b;
    cy += (r < b);
    rp[i] = r;
    ++i;
  }
  return cy;
}

/*不同位数的多精度数相加，返回最后的进位*/
unsigned int
mpn_add (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
/*@ default */
{
  unsigned int cy;
  /*@
    mpd_store_Z(UINT_MOD, ap, val_a, an) && an >= bn && bn >= 0
    which implies
      exists val_a_low val_a_high,
        val_a == val_a_low + val_a_high * Z::pow(UINT_MOD, bn) &&
        mpd_store_Z(UINT_MOD, ap, val_a_low, bn) *
        mpd_store_Z(UINT_MOD, ap + bn * sizeof(unsigned int), val_a_high, an - bn) 
    */
  /*@
    Given val_a_low val_a_high
   */
  /*@ an >= bn && bn >= 0 && UIntArray::undef_full(rp, an)
  which implies
    UIntArray::undef_full(rp, bn) *
    UIntArray::undef_full(rp + bn * sizeof(unsigned int), an - bn)
  */
  cy = mpn_add_n (rp, ap, bp, bn) /*@ where(implementation) val_a=val_a_low, val_b=val_b*/ ;
  /*@
  exists val_r_out, mpd_store_Z(UINT_MOD,rp, val_r_out, bn)
  which implies
    exists l_r,
    Zlength(l_r) == bn && 
    list_to_Z(UINT_MOD, l_r) == val_r_out && list_within_bound(UINT_MOD, l_r) &&
    UIntArray::full(rp, bn, l_r) 
  */
  /*@ 0 <= cy && cy <= UINT_MAX by local */
  if (an > bn) {
    cy = mpn_add_1 (rp + bn, ap + bn, an - bn, cy) /*@ where val=val_a_high*/;
  }
  return cy;
}

void gmp_umul_ppmm (unsigned int * w0, unsigned int * w1, unsigned int u, unsigned int v)
/*@ Require has_uint_permission(w0) *
            has_uint_permission(w1) 
    Ensure exists w0_value w1_value,
             w1_value * UINT_MOD + w0_value == u * v &&
             store_uint(w0, w0_value) *
             store_uint(w1, w1_value) */
{
      unsigned int __x0, __x1, __x2, __x3;
      unsigned __ul, __vl, __uh, __vh;
      unsigned int __u = (u), __v = (v);
      /*@ 0 <= u && u <= UINT_MAX by local */
      /*@ 0 <= v && v <= UINT_MAX by local */
      __ul = __u & 65535;
      __uh = __u >> 16;
      __vl = __v & 65535;
      __vh = __v >> 16;

      __x0 = (unsigned int) __ul * __vl;
      __x1 = (unsigned int) __ul * __vh;
      __x2 = (unsigned int) __uh * __vl;
      __x3 = (unsigned int) __uh * __vh;

      __x1 += __x0 >> 16; /* this can't give carry */
      __x1 += __x2; /* but this indeed can */
      if (__x1 < __x2)/* did we get it? */
        __x3 += 65536;	/* yes, add it in the proper pos. */
      * w1 = __x3 + (__x1 >> 16);
      * w0 = (__x1 << 16) + (__x0 & 65535);
}

/* 多精度数up × 乘单精度数vl，存储到 rp，返回进位 */
unsigned int mpn_mul_1(unsigned int * rp, unsigned int * up, int n, unsigned int vl)
/*@
  With l
  Require
    n > 0 && n <= INT_MAX && 0 <= vl && vl <= UINT_MAX &&
    Zlength(l) == n &&
    list_within_bound(UINT_MOD, l) &&
    UIntArray::full(up, n, l) *
    UIntArray::undef_full(rp, n)
  Ensure
    exists l' val',
    Zlength(l') == n &&
    list_within_bound(UINT_MOD, l') &&
    list_to_Z(UINT_MOD, l') == val' &&
    (val' + __return * Z::pow(UINT_MOD, n) == list_to_Z(UINT_MOD, l) * vl) &&
    UIntArray::full(up, n, l) *
    UIntArray::full(rp, n, l')
*/
{
  unsigned int ul, cl, hpl, lpl;
  int i;
  i = 0;
  cl = 0;
  /*@
    Inv
      exists l_rp,
      0 <= i && i <= n@pre &&
      0 <= cl && cl <= UINT_MAX &&
      Zlength(l_rp) == i &&
      list_within_bound(UINT_MOD, l_rp) &&
      (list_to_Z(UINT_MOD, l_rp) + cl * Z::pow(UINT_MOD, i) == list_to_Z(UINT_MOD, sublist(0, i, l)) * vl@pre) &&
      UIntArray::full(up@pre, n@pre, l) *
      UIntArray::seg(rp@pre, 0, i, l_rp) *
      UIntArray::undef_seg(rp@pre, i, n@pre)
  */
  while (i < n)
    {
      ul = up[i];
      gmp_umul_ppmm (&lpl, &hpl, ul, vl);
      /*@ 0 <= lpl && lpl <= UINT_MAX by local */
      /*@ 0 <= hpl && hpl <= UINT_MAX by local */
      /*@ Assert
            exists l_rp,
            rp == rp@pre && up == up@pre &&
            n == n@pre && vl == vl@pre &&
            0 <= i && i < n@pre &&
            0 <= cl && cl <= UINT_MAX &&
            0 <= lpl && lpl <= UINT_MAX &&
            0 <= hpl && hpl <= UINT_MAX &&
            Zlength(l_rp) == i &&
            list_within_bound(UINT_MOD, l_rp) &&
            (list_to_Z(UINT_MOD, l_rp) + cl * Z::pow(UINT_MOD, i) == list_to_Z(UINT_MOD, sublist(0, i, l)) * vl@pre) &&
            (hpl * UINT_MOD + lpl == l[i] * vl@pre) &&
            n@pre > 0 && n@pre <= INT_MAX &&
            0 <= vl@pre && vl@pre <= UINT_MAX &&
            Zlength(l) == n@pre &&
            list_within_bound(UINT_MOD, l) &&
            store_uint(&ul, l[i]) *
            UIntArray::full(up@pre, n@pre, l) *
            UIntArray::seg(rp@pre, 0, i, l_rp) *
            UIntArray::undef_seg(rp@pre, i, n@pre)
       */
      lpl += cl;
      cl = (lpl < cl) + hpl;
      rp[i] = lpl;
      i = i + 1;
    }
  return cl;
}

unsigned int
mpn_sub_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
/*@ default */
{
  /*@
    mpd_store_Z(UINT_MOD, ap, val, n)
    which implies
    exists l,
      Zlength(l) == n &&
      list_to_Z(UINT_MOD, l) == val && list_within_bound(UINT_MOD, l) &&
      UIntArray::full(ap, n, l)
  */
  /*@ Given l */
  int i;
  //assert (n > 0);
  i = 0;
  do
    {
      unsigned int a = ap[i];
      // Carry out
      unsigned int cy = a < b;
      rp[i] = a - b;
      b = cy;
      ++i;
    }
  /*@ Inv Assert
      exists data_rp_partial,
      rp == rp@pre && ap == ap@pre && n == n@pre &&
      0 < i && i <= n@pre &&
      0 <= b && b <= 1 &&
      Zlength(l) == n@pre &&
      Zlength(data_rp_partial) == i &&
      list_within_bound(UINT_MOD, l) &&
      list_within_bound(UINT_MOD, data_rp_partial) &&
      list_to_Z(UINT_MOD, l) == val &&
      UIntArray::full(ap@pre, n@pre, l) *
      UIntArray::seg(rp@pre, 0, i, data_rp_partial) *
      UIntArray::undef_seg(rp@pre, i, n@pre) &&
      (list_to_Z(UINT_MOD, data_rp_partial) - b * Z::pow(UINT_MOD, i) ==
       list_to_Z(UINT_MOD, sublist(0, i, l)) - b@pre)
  */
  while (i < n);

  return b;
}

unsigned int
mpn_sub_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
/*@ implementation
  With val_a val_b
  Require
    n >= 0 &&
    mpd_store_Z(UINT_MOD, ap, val_a, n) *
    mpd_store_Z(UINT_MOD, bp, val_b, n) *
    UIntArray::undef_full(rp, n)
  Ensure
    exists val_r,
    mpd_store_Z(UINT_MOD, ap, val_a, n) *
    mpd_store_Z(UINT_MOD, bp, val_b, n) *
    mpd_store_Z(UINT_MOD, rp, val_r, n) &&
    (val_r - __return * Z::pow(UINT_MOD, n) == val_a - val_b)
*/
{
  /*@
    mpd_store_Z(UINT_MOD, ap, val_a, n) * mpd_store_Z(UINT_MOD, bp, val_b, n)
    which implies
    exists l_a l_b,
      Zlength(l_a) == n && Zlength(l_b) == n &&
      list_to_Z(UINT_MOD, l_a) == val_a && list_within_bound(UINT_MOD, l_a) &&
      list_to_Z(UINT_MOD, l_b) == val_b && list_within_bound(UINT_MOD, l_b) &&
      UIntArray::full(ap, n, l_a) * UIntArray::full(bp, n, l_b)
  */
  /*@ Given l_a l_b */
  int i;
  unsigned int cy;

  i = 0;
  cy = 0;
  /*@ Inv Assert
      exists data_rp_partial,
      rp == rp@pre && ap == ap@pre && bp == bp@pre && n == n@pre &&
      0 <= i && i <= n@pre &&
      0 <= cy && cy <= 2 &&
      Zlength(l_a) == n@pre && Zlength(l_b) == n@pre &&
      Zlength(data_rp_partial) == i &&
      list_within_bound(UINT_MOD, l_a) &&
      list_within_bound(UINT_MOD, l_b) &&
      list_within_bound(UINT_MOD, data_rp_partial) &&
      list_to_Z(UINT_MOD, l_a) == val_a &&
      list_to_Z(UINT_MOD, l_b) == val_b &&
      UIntArray::full(ap@pre, n@pre, l_a) *
      UIntArray::full(bp@pre, n@pre, l_b) *
      UIntArray::seg(rp@pre, 0, i, data_rp_partial) *
      UIntArray::undef_seg(rp@pre, i, n@pre) &&
      (list_to_Z(UINT_MOD, data_rp_partial) - cy * Z::pow(UINT_MOD, i) ==
       list_to_Z(UINT_MOD, sublist(0, i, l_a)) - list_to_Z(UINT_MOD, sublist(0, i, l_b)))
  */
  for (; i < n; i++)
    {
      unsigned int a, b;
      a = ap[i]; b = bp[i];
      b += cy;
      cy = (b < cy);
      cy += (a < b);
      rp[i] = a - b;
    }
  return cy;
}

unsigned int
mpn_sub (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
/*@ implementation
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
{
  unsigned int cy;
  //assert (an >= bn);
  /*@ an >= bn && an > 0 && bn >= 0 &&
      mpd_store_Z(UINT_MOD, ap, val_a, an)
      which implies
      exists val_a_lo val_a_hi,
      (val_a == val_a_lo + val_a_hi * Z::pow(UINT_MOD, bn)) &&
      mpd_store_Z(UINT_MOD, ap, val_a_lo, bn) *
      mpd_store_Z(UINT_MOD, ap + (bn * sizeof(unsigned int)), val_a_hi, an - bn)
  */
  /*@ Given val_a_lo val_a_hi */
  /*@ an >= bn && bn >= 0 &&
      UIntArray::undef_full(rp, an)
      which implies
      UIntArray::undef_full(rp, bn) *
      UIntArray::undef_full(rp + (bn * sizeof(unsigned int)), an - bn)
  */
  cy = mpn_sub_n (rp, ap, bp, bn) /*@ where(implementation) val_a=val_a_lo, val_b=val_b */;
  /*@
    exists val_r_out, mpd_store_Z(UINT_MOD, rp, val_r_out, bn)
    which implies
    exists l_r,
      Zlength(l_r) == bn &&
      list_to_Z(UINT_MOD, l_r) == val_r_out && list_within_bound(UINT_MOD, l_r) &&
      UIntArray::full(rp, bn, l_r)
  */
  /*@ 0 <= cy && cy <= UINT_MAX by local */
  if (an > bn) {
    /*@ an > bn && an - bn > 0 */
    cy = mpn_sub_1 (rp + bn, ap + bn, an - bn, cy) /*@ where val=val_a_hi */;
  }
  return cy;
}

/* MPZ interface */

void
mpz_clear (mpz_t r)
/*@ default */
{
  if (r->_mp_alloc)
    gmp_free_limbs (r->_mp_d, r->_mp_alloc) ;
}

static unsigned int *
mpz_realloc (mpz_t r, int size)
/*@ default */
{
  size = gmp_max (size, 1);

  if (r->_mp_alloc)
    r->_mp_d = gmp_realloc_limbs (r->_mp_d, r->_mp_alloc, size);
  else
    r->_mp_d = gmp_alloc_limbs (size);
  r->_mp_alloc = size;

  if (gmp_abs (r->_mp_size) > size)
    r->_mp_size = 0;

  return r->_mp_d;
}

/* Realloc for an mpz_t WHAT if it has less than NEEDED limbs.  */
unsigned int *mrz_realloc_if(mpz_t z,int n)
/*@ default */
{
  if (n > z->_mp_alloc) return mpz_realloc(z, n);
  return z->_mp_d;
  // ret = n > z->_mp_alloc ? mpz_realloc(z, n)  : z->_mp_d;
  // return ret;
}

/* MPZ comparisons and the like. */
int
mpz_sgn (const mpz_t u)
/*@ default */
{
  return gmp_cmp (u->_mp_size, 0);
}

void
mpz_swap (mpz_t u, mpz_t v)
/*@
  With
    n m
  Require
    store_Z(u, n) * store_Z(v, m)
  Ensure
    store_Z(u, m) * store_Z(v, n)
*/
{
  int_swap (&u->_mp_alloc, &v->_mp_alloc);
  mp_ptr_swap(&u->_mp_d, &v->_mp_d);
  int_swap (&u->_mp_size, &v->_mp_size);
}

/* MPZ addition and subtraction */
static int
mpz_abs_add (mpz_t r, const mpz_t a, const mpz_t b)
/*@ With n m l
  Require
    store_Z(a, n) * store_Z(b, m) * store_Z(r, l)
  Ensure
    store_Z(a, n) * store_Z(b, m) *
    store_Z_remain_size(r, Zabs(n) + Zabs(m), __return)
*/
{
  int an = gmp_abs (a->_mp_size);
  int bn = gmp_abs (b->_mp_size);
  unsigned int *rp;
  unsigned int cy;

  if (an < bn)
  {
    mpz_srcptr_swap (&a, &b);
    int_swap (&an, &bn);
  }
  /*@ Assert 
      exists n_new m_new aptr bptr asize bsize acap bcap rptr rsize rcap, 
      Permutation((cons(Prod2(a, n_new), cons(Prod2(b, m_new), nil))), 
                   cons(Prod2(a@pre, n), cons(Prod2(b@pre, m), nil))) &&
      an >= bn && an == Zabs(asize) && bn == Zabs(bsize) &&
      an <= acap && bn <= bcap && r == r@pre &&
      same_sign(n_new, asize) && same_sign(m_new, bsize) &&
      Zabs(rsize) <= rcap && same_sign(l, rsize) && rcap >= 0 &&
      has_permission(&cy) * has_permission(&rp) *
      store(&(a->_mp_d), aptr) *
      store(&(a->_mp_size), asize) * 
      store(&(a->_mp_alloc), acap) * 
      store(&(b->_mp_d), bptr) *
      store(&(b->_mp_size), bsize) * 
      store(&(b->_mp_alloc), bcap) *
      store(&(r->_mp_d), rptr) *
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap) *
      UIntArray::undef_seg(aptr, an, acap) *
      UIntArray::undef_seg(bptr, bn, bcap) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      mpd_store_Z_compact(UINT_MOD, aptr, Zabs(n_new), an) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(m_new), bn) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(l), Zabs(rsize))
  */
  rp = mrz_realloc_if (r, an + 1);
  /*@ Assert
      exists n_new m_new aptr bptr asize bsize acap bcap rsize rcap,
      Permutation((cons(Prod2(a, n_new), cons(Prod2(b, m_new), nil))),
                   cons(Prod2(a@pre, n), cons(Prod2(b@pre, m), nil))) &&
      an >= bn && an == Zabs(asize) && bn == Zabs(bsize) &&
      an <= acap && bn <= bcap && r == r@pre &&
      same_sign(n_new, asize) && same_sign(m_new, bsize) &&
      same_sign(l, rsize) && Zabs(rsize) <= rcap && rcap >= 0 &&
      r->_mp_size == rsize &&
      r->_mp_alloc == Z::max(Z::max(an + 1, 1), rcap) &&
      r->_mp_d == rp &&
      is_compact_Z(UINT_MOD, Zabs(l), Zabs(rsize)) &&
      an < Z::max(Z::max(an + 1, 1), rcap) &&
      has_permission(&cy) *
      store(&(a->_mp_d), aptr) *
      store(&(a->_mp_size), asize) *
      store(&(a->_mp_alloc), acap) *
      store(&(b->_mp_d), bptr) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      UIntArray::undef_seg(aptr, an, acap) *
      UIntArray::undef_seg(bptr, bn, bcap) *
      mpd_store_Z_compact(UINT_MOD, aptr, Zabs(n_new), an) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(m_new), bn) *
      UIntArray::undef_full(rp, an) *
      UIntArray::undef_seg(rp, an, Z::max(Z::max(an + 1, 1), rcap))   
  */
  cy = mpn_add (rp, a->_mp_d, an, b->_mp_d, bn);
  rp[an] = cy;
  return an + cy;
}

/* MPZ addition and subtraction */
static int
mpz_abs_sub (mpz_t r, const mpz_t a, const mpz_t b)
/*@ With n m l
  Require
    store_Z(a, n) * store_Z(b, m) * store_Z(r, l)
  Ensure
    store_Z(a, n) * store_Z(b, m) *
    store_Z_remain_size(r, Zabs(n) - Zabs(m), __return)
*/
{
  int an = gmp_abs (a->_mp_size);
  int bn = gmp_abs (b->_mp_size);
  int cmp;
  unsigned int *rp;
  cmp = mpn_cmp4 (a->_mp_d, an, b->_mp_d, bn); 
  if (cmp > 0)
  {
      /*@ Assert
      exists rptr rsize rcap,
      cmp > 0 && Zabs(n) > Zabs(m) && cmp == 1 &&
      bn == Zabs(b@pre->_mp_size) &&
      same_sign(m, b@pre->_mp_size) &&
      Zabs(b@pre->_mp_size) <= b@pre->_mp_alloc &&
      an == Zabs(a@pre->_mp_size) &&
      same_sign(n, a@pre->_mp_size) &&
      Zabs(a@pre->_mp_size) <= a@pre->_mp_alloc &&
      Zabs(rsize) <= rcap && same_sign(l, rsize) && rcap >= 0 &&
      mpd_store_Z_compact(UINT_MOD, a@pre->_mp_d, Zabs(n), an) *
      mpd_store_Z_compact(UINT_MOD, b@pre->_mp_d, Zabs(m), bn) *
      has_permission(&rp) *
      UIntArray::undef_seg(b@pre->_mp_d, Zabs(b@pre->_mp_size), b@pre->_mp_alloc) *
      UIntArray::undef_seg(a@pre->_mp_d, Zabs(a@pre->_mp_size), a@pre->_mp_alloc) *
      store(&(r->_mp_d), rptr) *
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(l), Zabs(rsize)) *
      (b == b@pre) * (a == a@pre) * (r == r@pre)
      */
      rp = mrz_realloc_if (r, an);
      /*@ Assert
      exists rsize rcap,
      cmp > 0 && Zabs(n) > Zabs(m) && cmp == 1 &&
      bn == Zabs(b@pre->_mp_size) &&
      same_sign(m, b@pre->_mp_size) &&
      Zabs(b@pre->_mp_size) <= b@pre->_mp_alloc &&
      an == Zabs(a@pre->_mp_size) &&
      same_sign(n, a@pre->_mp_size) &&
      Zabs(a@pre->_mp_size) <= a@pre->_mp_alloc &&
      same_sign(l, rsize) && Zabs(rsize) <= rcap && rcap >= 0 &&
      r->_mp_size == rsize &&
      r->_mp_alloc == Z::max(Z::max(an, 1), rcap) &&
      r->_mp_d == rp &&
      is_compact_Z(UINT_MOD, Zabs(l), Zabs(rsize)) &&
      an < Z::max(Z::max(an + 1, 1), rcap) &&
      mpd_store_Z_compact(UINT_MOD, a@pre->_mp_d, Zabs(n), an) *
      mpd_store_Z_compact(UINT_MOD, b@pre->_mp_d, Zabs(m), bn) *
      UIntArray::undef_seg(b@pre->_mp_d, Zabs(b@pre->_mp_size), b@pre->_mp_alloc) *
      UIntArray::undef_seg(a@pre->_mp_d, Zabs(a@pre->_mp_size), a@pre->_mp_alloc) *
      (b == b@pre) * (a == a@pre) * (r == r@pre) *
      UIntArray::undef_full(rp, an) *
      UIntArray::undef_seg(rp, an, Z::max(Z::max(an, 1), rcap))   
      */
      mpn_sub (rp, a->_mp_d, an, b->_mp_d, bn) /*@ where(implementation) */;
      return mpn_normalized_size (rp, an);
    }
  else if (cmp < 0)
  {
      /*@ Assert
      exists rptr rsize rcap,
      cmp < 0 && cmp <= 0 && Zabs(n) < Zabs(m) && cmp == -1 &&
      bn == Zabs(b@pre->_mp_size) &&
      same_sign(m, b@pre->_mp_size) &&
      Zabs(b@pre->_mp_size) <= b@pre->_mp_alloc &&
      an == Zabs(a@pre->_mp_size) &&
      same_sign(n, a@pre->_mp_size) &&
      Zabs(a@pre->_mp_size) <= a@pre->_mp_alloc &&
      Zabs(rsize) <= rcap && same_sign(l, rsize) && rcap >= 0 &&
      mpd_store_Z_compact(UINT_MOD, a@pre->_mp_d, Zabs(n), an) *
      mpd_store_Z_compact(UINT_MOD, b@pre->_mp_d, Zabs(m), bn) *
      has_permission(&rp) *
      UIntArray::undef_seg(b@pre->_mp_d, Zabs(b@pre->_mp_size), b@pre->_mp_alloc) *
      UIntArray::undef_seg(a@pre->_mp_d, Zabs(a@pre->_mp_size), a@pre->_mp_alloc) *
      store(&(r->_mp_d), rptr) *
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(l), Zabs(rsize)) *
      (b == b@pre) * (a == a@pre) * (r == r@pre)
      */
      rp = mrz_realloc_if (r, bn);
      /*@ Assert
      exists rsize rcap,
      cmp < 0 && cmp <= 0 && Zabs(n) < Zabs(m) && cmp == -1 &&
      bn == Zabs(b@pre->_mp_size) &&
      same_sign(m, b@pre->_mp_size) &&
      Zabs(b@pre->_mp_size) <= b@pre->_mp_alloc &&
      an == Zabs(a@pre->_mp_size) &&
      same_sign(n, a@pre->_mp_size) &&
      Zabs(a@pre->_mp_size) <= a@pre->_mp_alloc &&
      same_sign(l, rsize) && Zabs(rsize) <= rcap && rcap >= 0 &&
      r->_mp_size == rsize &&
      r->_mp_alloc == Z::max(Z::max(bn, 1), rcap) &&
      r->_mp_d == rp &&
      is_compact_Z(UINT_MOD, Zabs(l), Zabs(rsize)) &&
      bn < Z::max(Z::max(bn + 1, 1), rcap) &&
      mpd_store_Z_compact(UINT_MOD, a@pre->_mp_d, Zabs(n), an) *
      mpd_store_Z_compact(UINT_MOD, b@pre->_mp_d, Zabs(m), bn) *
      UIntArray::undef_seg(b@pre->_mp_d, Zabs(b@pre->_mp_size), b@pre->_mp_alloc) *
      UIntArray::undef_seg(a@pre->_mp_d, Zabs(a@pre->_mp_size), a@pre->_mp_alloc) *
      (b == b@pre) * (a == a@pre) * (r == r@pre) *
      UIntArray::undef_full(rp, bn) *
      UIntArray::undef_seg(rp, bn, Z::max(Z::max(bn, 1), rcap))   
      */
      mpn_sub (rp, b->_mp_d, bn, a->_mp_d, an) /*@ where(implementation) */;
      return -mpn_normalized_size (rp, bn);
    }
  else
  {
    return 0;
  }
}


void
mpz_add (mpz_t r, const mpz_t a, const mpz_t b)
/*@ With n m l
  Require
    store_Z(a, n) * store_Z(b, m) * store_Z(r, l)
  Ensure
    store_Z(a, n) * store_Z(b, m) *
    store_Z(r, n + m)
*/
{
  int rn;
  if ( (a->_mp_size ^ b->_mp_size) >= 0) {
    rn = mpz_abs_add (r, a, b);
  }
  else{
    rn = mpz_abs_sub (r, a, b);
  }
  r->_mp_size = a->_mp_size >= 0 ? rn : - rn;
}


void
mpz_sub (mpz_t r, const mpz_t a, const mpz_t b)
/*@ With n m l
  Require
    store_Z(a, n) * store_Z(b, m) * store_Z(r, l)
  Ensure
    store_Z(a, n) * store_Z(b, m) *
    store_Z(r, n - m)
*/
{
  int rn;
  if ( (a->_mp_size ^ b->_mp_size) >= 0)
  {
    rn = mpz_abs_sub (r, a, b);
  }
  else{
    rn = mpz_abs_add (r, a, b);
  }
  r->_mp_size = a->_mp_size >= 0 ? rn : - rn;
}
