/*@ Import Coq Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib */

/*@
  Extern Coq (Zabs : Z -> Z)
             (Zgcd : Z -> Z -> Z)
             (Zmax : Z -> Z -> Z)
             (Z::max : Z -> Z -> Z)
             (Z::min : Z -> Z -> Z)
             (Z::pow : Z -> Z -> Z)
             (Z::quot : Z -> Z -> Z)
             (mpd_store_Z : Z -> Z -> Z -> Z -> Assertion)
             (mpd_store_Z_compact : Z -> Z -> Z -> Z -> Assertion)
             (mpd_store_Z_compact_read0 : Z -> Z -> Z -> Assertion)
             (is_compact_Z : Z -> Z -> Z -> Prop)
             (normalized_size_read0_guard : Z -> list Z -> Prop)
             (store_Z_remain_size : Z -> Z -> Z -> Assertion)
             (store_Z_with_old_size : Z -> Z -> Z -> Z -> Assertion)
             (same_sign : Z -> Z -> Prop)
             (same_sign_or_zero : Z -> Z -> Prop)
             (mpz_mul_sign : Z -> Z -> Z -> Prop)
             (mpz_mul_2exp_fits : Z -> Z -> Prop)
             (mpz_one_limb_headroom : Z -> Prop)
             (list_to_Z : Z -> list Z -> Z)
             (list_within_bound : Z -> list Z -> Prop)
             (last : list Z -> Z -> Z)
             (mpd_read0_data : list Z -> list Z)
             (UINT_MOD : Z)
*/

/*@ Extern Coq (store_Z : Z -> Z -> Assertion)
               (store_Z_dummy : Z -> Z -> Assertion)
               (store_Z_read0 : Z -> Z -> Assertion)
               (optional_store_Z : Z -> Z -> Assertion)
               (optional_q_undef : Z -> Z -> Assertion)
               (optional_q_full : Z -> Z -> list Z -> Assertion) */

/*@ Extern Coq (div_inverse_slot : Z -> Assertion)
               (store_div_inverse : Z -> Z -> Z -> Assertion)
               (store_preinv_divisor : Z -> Z -> Z -> Z -> Assertion)
               (valid_mpz_div_round_mode : Z -> Prop)
               (mpz_div_qr_math : Z -> Z -> Z -> Z -> Z -> Prop)
               (mpz_div_qr_ret_ok : Z -> Z -> Prop) */

/*@ Extern Coq (mpn_common_scan_found : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
               (mpn_scan1_found : list Z -> Z -> Z -> Z -> Z -> Prop)
               (gmp_scan_limb : Z -> Z -> Z)
               (mpn_common_scan_target : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
               (mpn_common_scan_result : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
               (mpn_scan1_target : list Z -> Z -> Prop)
               (mpn_scan1_result : list Z -> Z -> Z -> Prop) */

/*@ include strategies "gmp.strategies" */
/*@ include strategies "gmp_optional.strategies" */

typedef struct __mpz_struct {
    int _mp_alloc;
    int _mp_size;
    unsigned int *_mp_d;
} __mpz_struct;

typedef __mpz_struct mpz_t[1];
typedef __mpz_struct *mpz_ptr;
typedef const __mpz_struct *mpz_srcptr;

static const unsigned int mpz_dummy_limb = 0xc1a0;

struct gmp_div_inverse {
    unsigned int shift;
    unsigned int d1;
    unsigned int d0;
    unsigned int di;
};
