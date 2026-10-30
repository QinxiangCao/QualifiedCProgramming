/*@ 
  Extern Coq (Zabs : Z -> Z) 
             (Z::max : Z -> Z -> Z)
             (Z::pow : Z -> Z -> Z)
             (mpd_store_Z : Z -> Z -> Z -> Z -> Assertion)
             (mpd_store_Z_compact: Z -> Z -> Z -> Z -> Assertion)
             (mpd_store_list : list Z -> Z -> Assertion)
             (is_compact_Z: Z -> Z -> Z -> Prop)
             (store_Z: Z -> Z -> Assertion)
             (store_Z_remain_size: Z -> Z -> Z -> Assertion)
             (same_sign: Z -> Z -> Prop)
             (list_to_Z : Z -> list Z -> Z)
             (list_within_bound: Z -> list Z -> Prop)
             (last: list Z -> Z -> Z)
             (UINT_MOD: Z)
             (Permutation : {A} -> list A -> list A -> Prop)
             (Prod2 : Z -> Z-> Z * Z)
*/

/*@ Import Coq Require Import SimpleC.EE.Applications_human.minigmp.GmpAux SimpleC.EE.Applications_human.minigmp.GmpNumber */
/*@ Import Coq Import Aux */


typedef struct __mpz_struct
{
  int _mp_alloc;		/* Number of *limbs* allocated and pointed
				                to by the _mp_d field.  */
  int _mp_size;			/* abs(_mp_size) is the number of limbs the
				                last field points to.  If _mp_size is
				                negative this is a negative number.  */
  unsigned int *_mp_d;		/* Pointer to the limbs.  */
} __mpz_struct;

/* mpz_t is an array type that contains a single element of __mpz_struct, acting as a reference. */
typedef __mpz_struct mpz_t[1];
typedef __mpz_struct *mpz_ptr;
typedef const __mpz_struct *mpz_srcptr;

/* BEGIN Given Functions */

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

int gmp_max(int a, int b)
/*@
  Require emp
  Ensure __return == Z::max(a, b)
*/;

int gmp_cmp(int a, int b)
/*@
  Require emp
  Ensure 
    emp * 
    (a > b && __return == 1 || 
    a == b && __return == 0 ||
    a < b && __return == -1)
*/;


/* Swap functions. */
void int_swap(int *x, int *y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x == py && *y == px
*/
;

void mp_ptr_swap(unsigned int **x, unsigned int **y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x == py && *y == px
*/
;

void mpz_srcptr_swap(mpz_srcptr *x, mpz_srcptr *y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x == py && *y == px
*/
;

/* Memory allocation functions. */
static unsigned int *
gmp_alloc_limbs (int size)
/*@
  Require
    size >= 0
  Ensure
    UIntArray::undef_full(__return, size)
*/;

static unsigned int *
gmp_realloc_limbs (unsigned int *old, int old_size, int size)
/*@
  With
    len n
  Require
    old_size >= 0 && size >= old_size &&
    mpd_store_Z_compact(UINT_MOD, old, n, len) *
    UIntArray::undef_seg(old, len, old_size)
  Ensure
    mpd_store_Z_compact(UINT_MOD,__return, n, len) *
    UIntArray::undef_seg(__return, len, size)
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
*/
;

/* END Given Functions  */

void mpn_copyi (unsigned int *d, unsigned int *s, int n)
/*@
  With val
  Require
    mpd_store_Z(UINT_MOD, s, val, n) *
    UIntArray::undef_full(d, n)
  Ensure 
    mpd_store_Z(UINT_MOD,s, val, n) *
    mpd_store_Z(UINT_MOD,d, val, n)
*/;

int mpn_cmp (unsigned int *ap, unsigned int *bp, int n)
/*@
  With val1 val2
  Require
    0 <= n &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, n)  
  Ensure
    (val1 > val2 && __return == 1 ||
    val1 == val2 && __return == 0 ||
    val1 < val2 && __return == -1) &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, n)
*/;

static int mpn_cmp4 (unsigned int *ap, int an, unsigned int *bp, int bn)
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

static int mpn_normalized_size (unsigned int *xp, int n)
/*@
  With val
  Require
    0 <= n && 
    mpd_store_Z(UINT_MOD, xp, val, n) 
  Ensure
    0 <= __return && __return <= n &&
    mpd_store_Z_compact(UINT_MOD, xp, val, __return) * 
    UIntArray::undef_seg(xp, __return, n)
*/;

unsigned int mpn_add_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
/*@
  With val
  Require
    n > 0 && 0 <= b && b <= UINT_MAX &&
    mpd_store_Z(UINT_MOD,ap, val, n) *
    UIntArray::undef_full(rp, n)
  Ensure
    exists val',
    mpd_store_Z(UINT_MOD, ap, val, n) *
    mpd_store_Z(UINT_MOD, rp, val', n) &&
    (val' + __return * Z::pow(UINT_MOD, n) == val + b)
*/;
unsigned int mpn_add_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
/*@ default <= implementation
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
*/;

unsigned int mpn_add (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
/*@ 
 With val_a val_b
 Require
   an >= bn && an >= 0 && bn >= 0 &&
   mpd_store_Z(UINT_MOD, ap, val_a, an) *
   mpd_store_Z(UINT_MOD, bp, val_b, bn) *
   UIntArray::undef_full(rp, an)
 Ensure
   exists val_r_out,
   (val_r_out + __return * Z::pow(UINT_MOD, an) == val_a + val_b) &&
   mpd_store_Z(UINT_MOD, ap, val_a, an) *
   mpd_store_Z(UINT_MOD, bp, val_b, bn) *
   mpd_store_Z(UINT_MOD, rp, val_r_out, an)
*/;

// unsigned int mpn_sub_1 (unsigned int *, unsigned int *, int, unsigned int);
// unsigned int mpn_sub_n (unsigned int *, unsigned int *, unsigned int *, int);
// unsigned int mpn_sub (unsigned int *, unsigned int *, int, unsigned int *, int);
unsigned int mpn_sub_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
/*@
  With val
  Require
    n > 0 && 0 <= b && b <= UINT_MAX &&
    mpd_store_Z(UINT_MOD, ap, val, n) *
    UIntArray::undef_full(rp, n)
  Ensure
    exists val',
    mpd_store_Z(UINT_MOD, ap, val, n) *
    mpd_store_Z(UINT_MOD, rp, val', n) &&
    (val' - __return * Z::pow(UINT_MOD, n) == val - b@pre)
*/;

unsigned int mpn_sub_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
/*@ default <= implementation
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
*/;

unsigned int mpn_sub (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
/*@ default <= implementation
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

void mpz_neg (mpz_t u, const mpz_t v)
/*@
  With
    n m
  Require
    store_Z(u, n) * store_Z(v, m)
  Ensure
    store_Z(u, -m) * store_Z(v, m)
*/;
void mpz_swap (mpz_t u, mpz_t v);

void mpz_add (mpz_t r, const mpz_t a, const mpz_t b);
void mpz_sub (mpz_t r, const mpz_t a, const mpz_t b);

void mpz_set (mpz_t, const mpz_t);


/* MPZ interface */

static unsigned int *
mpz_realloc (mpz_t r, int size)
/*@
  With
    ptr old cap n
  Require
    size >= cap && size <= INT_MAX && cap >= 0 && cap <= INT_MAX &&
    Zabs(old) <= cap && same_sign(n, old) &&
    mpd_store_Z_compact(UINT_MOD,ptr, Zabs(n), Zabs(old)) * UIntArray::undef_seg(ptr, Zabs(old), cap) &&
      r -> _mp_size == old &&
      r -> _mp_alloc == cap &&
      r -> _mp_d == ptr
  Ensure 
    same_sign(n, old) &&
    mpd_store_Z_compact(UINT_MOD,__return, Zabs(n), Zabs(old)) * UIntArray::undef_seg(__return, Zabs(old), Z::max(size,1)) &&
    r -> _mp_size == old &&
    r -> _mp_alloc == Z::max(size,1) &&
    r -> _mp_d == __return
*/;

/* Realloc for an mpz_t WHAT if it has less than NEEDED limbs.  */
unsigned int *mrz_realloc_if(mpz_t z,int n)
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



/*@ include strategies "gmp.strategies" */
