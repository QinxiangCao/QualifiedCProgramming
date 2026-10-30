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

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

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
*/
;

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

void mpz_neg (mpz_t u, const mpz_t v)
/*@ exported <= default
  With
    n m
  Require
    store_Z(u, n) * store_Z(v, m)
  Ensure
    store_Z(u, -m) * store_Z(v, m)
*/;
/*@ include strategies "gmp.strategies" */
