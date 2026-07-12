Version 4.2.2
-------------

* ensured compatibility with Coq Stdlib up to 9.1.0

Version 4.2.1
-------------

* made Coq 8.15 the minimal version and removed the `Int63Compat` and `Nat2Z_compat` layers
* ensured compatibility from Coq 8.15 to 9.0

Version 4.2.0
-------------

* added `SF2B'` as a proof-free variant of `SF2B`
* fixed installation of `Pff2Flocq`
* ensured compatibility from Coq 8.12 to 8.20

Version 4.1.4
-------------

* ensured compatibility from Coq 8.12 to 8.19

Version 4.1.3
-------------

* avoided breaking users of `IEEE754.PrimFloat`

Version 4.1.2
-------------

* ensured compatibility from Coq 8.12 to 8.18

Version 4.1.1
-------------

* ensured compatibility from Coq 8.12 to 8.17

Version 4.1.0
-------------

* added `Bnearbyint` and `Btrunc` in `IEEE754`
* ensured compatibility from Coq 8.12 to 8.16

Version 4.0.0
-------------

* made Coq 8.12 the minimal version and removed the `IEEE754.SpecFloatCompat` layer
* removed automatic export of `ZArith` and `Reals` from `Core.Raux` and `Core.Core`
* proved a close/far-path adder in `Calc.Plus`
* made `IEEE754.Binary` a wrapper around `IEEE754.BinarySingleNaN`

Version 3.4.3
-------------

* ensured compatibility from Coq 8.7 to 8.15

Version 3.4.2
-------------

* restored compatibility with Coq 8.11

Version 3.4.1
-------------

* ensured compatibility from Coq 8.7 to 8.14

Version 3.4.0
-------------

* added some comparison functions to `IEEE754.BinarySingleNaN`
* proved the corresponding adequacy lemmas in `IEEE754.PrimFloat`

Version 3.3.1
-------------

* fixed failure when extracting to OCaml

Version 3.3.0
-------------

* added `IEEE754.BinarySingleNaN` where NaN have no payload
* proved adequacy of Coq 8.11 floating-point numbers in `IEEE754.PrimFloat`
* added theorems about rounding to nearest, tie breaking to zero

Version 3.2.1
-------------

* ensured compatibility from Coq 8.7 to 8.11

Version 3.2.0
-------------

* added function `Bfma`
* ensured compatibility from Coq 8.7 to 8.10

Version 3.1.0
-------------

* changed matching order in `Bcompare`
* improved behavior of `IEEE754.Binary` functions with respect to NaNs
* ensured compatibility from Coq 8.7 to 8.9
* added functions `Bpred` and `Bsucc`
* added theorems on optimal relative error bounds for plus and square root
* made installation also install source files

Version 3.0.0
-------------

* stripped the `F*_` prefix from all the file names, renamed some files:
  - `Definitions -> Defs`
  - `Appli -> IEEE754`
* renamed `ln_beta` into `mag`
* renamed `canonic_exp` into `cexp`, `canonic` into `canonical`
* renamed all theorems ending with `unicity` by `unique`
* changed `FLX_`, `FIX_`, `FLT_`, `FLXN_`, `FTZ_format` into inductive types
* changed `nan_pl` into a boolean predicate
* replaced `Z2R` with Coq 8.7's `IZR`
* removed `Zeven` and its theorems in favor of `Z.even` of the standard library
* modified statements of `Rcompare_sqr`, `ulp_DN`, `mult_error_FLT`, `mag_div`
* added theorems about the remainder being in the format (in `Div_sqrt_error.v`)
* made `Fdiv_core` and `Fsqrt_core` generic with respect to the format
* renamed theorems more uniformly:
  - `bpow_plus1 -> bpow_plus_1`
  - `mag_lt_pos -> lt_mag`
  - `F2R_le_reg -> le_F2R`
  - `F2R_le_compat -> F2R_le`
  - `F2R_lt_reg -> lt_F2R`
  - `F2R_lt_compat -> F2R_lt`
  - `F2R_eq_reg -> eq_F2R`
  - `F2R_eq_compat -> F2R_eq`
  - `F2R_eq_0_reg -> eq_0_F2R`
  - `F2R_ge_0_reg -> ge_0_F2R`
  - `F2R_le_0_reg -> le_0_F2R`
  - `F2R_gt_0_reg -> gt_0_F2R`
  - `F2R_lt_0_reg -> lt_0_F2R`
  - `F2R_le_0_compat -> F2R_le_0`
  - `F2R_ge_0_compat -> F2R_ge_0`
  - `F2R_gt_0_compat -> F2R_gt_0`
  - `F2R_lt_0_compat -> F2R_lt_0`
  - `F2R_neq_0_compat -> F2R_neq_0`
  - `Fnum_ge_0_compat -> Fnum_ge_0`
  - `Fnum_le_0_compat -> Fnum_le_0`
  - `round_ZR_pos -> round_ZR_DN`
  - `round_ZR_neg -> round_ZR_UP`
  - `round_AW_pos -> round_ZR_UP`
  - `round_AW_neg -> round_ZR_DN`
  - `Znearest_N -> Znearest_half`
  - `Rnd_DN_UP_pt_N -> Rnd_N_pt_DN_UP`
  - `Rnd_DN_pt_N -> Rnd_N_pt_DN`
  - `Rnd_UP_pt_N -> Rnd_N_pt_UP`
  - `Rnd_DN_UP_pt_sym -> Rnd_UP_pt_opp`
  - `Rnd_UP_DN_pt_sym -> Rnd_DN_pt_opp`
  - `Rnd_DN_UP_sym -> Rnd_DN_opp`
  - `Rnd_N_pt_sym -> Rnd_N_pt_opp_inv`
  - `Rnd_N_pt_pos -> Rnd_N_pt_ge_0`
  - `Rnd_N_pt_neg -> Rnd_N_pt_le_0`
  - `Rnd_NG_pt_sym -> Rnd_NG_pt_opp_inv`
  - `Rnd_NA_N_pt -> Rnd_NA_pt_N`
  - `Rnd_odd_pt_sym -> Rnd_odd_pt_opp_inv`
  - `le_pred_lt -> pred_ge_gt`
  - `lt_succ_le -> succ_gt_ge`
  - `le_round_DN_lt_UP -> round_DN_ge_UP_gt`
  - `round_UP_le_gt_DN -> round_UP_le_DN_lt`
  - `round_DN_eq_betw -> round_DN_eq`
  - `round_UP_eq_betw -> round_UP_eq`
  - `round_plus_eq_zero -> round_plus_neq_0` (and modified statement)
  - `round_odd_prop -> round_N_odd`
  - `double_round_*_beta_ge_* -> round_round_*_radix_ge_*`
  - `double_round_* -> round_round_*`

Version 2.6.1
-------------

* ensured compatibility from Coq 8.4 to 8.8

Version 2.6.0
-------------

* ensured compatibility from Coq 8.4 to 8.7
* removed some hypotheses on some lemmas of `Fcore_ulp`
* added lemmas to `Fprop_plus_error`
* improved examples

Version 2.5.2
-------------

* ensured compatibility from Coq 8.4 to 8.6

Version 2.5.1
-------------

* ensured compatibility with both Coq 8.4 and 8.5

Version 2.5.0
-------------

* ensured compatibility with both Coq 8.4 and 8.5
  (Flocq now provides its own version of `iter_pos`)
* redefined `ulp`, so that `ulp 0` is meaningful
* renamed, generalized, and added lemmas in `Fcore_ulp`
* extended predecessor and successor to nonpositive values
  (the previous definition of `pred` has been renamed `pred_pos`)
* removed some hypotheses on lemmas of `Fprop_relative.v`
* added more examples
  - `Average`: proof on Sterbenz's average and correctly-rounded average
  - `Cody_Waite`: Cody & Waite's approximation of exponential
  - `Compute`: effective FP computations with an example of `sqrt(sqr(x))`
     in radix 5 and precision 3
  - `Division_u16`: integer division using floating-point FMA
  - `Triangle`: Kahan's algorithm for the area of a triangle

Version 2.4.0
-------------

* moved some lemmas from `Fcalc_digits.v` to `Fcore_digits.v` and made them axiom-free
* added theorems about double rounding being innocuous (`Fappli_double_round.v`)
* added example about double rounding in odd radix
* improved a bit the efficiency of IEEE-754 arithmetic

Version 2.3.0
-------------

* moved some lemmas from `Fcalc_digits.v` to `Fcore_digits.v` and made them axiom-free
* used the square root from the standard library instead of a custom one
* added an example about `sqrt(sqr(x))`

Version 2.2.2
-------------

* fixed `install` target for case-insensitive filesystems

Version 2.2.1
-------------

* fixed regeneration of `Flocq_version.v`

Version 2.2.0
-------------

* added theorems about rounding to odd and double rounding
* improved handling of special values of IEEE-754 arithmetic

Version 2.1.0
-------------

* ensured compatibility with both Coq 8.3 and 8.4
* improved support for rounding toward and away from zero
* proved that formats are stable by arbitrary rounding or ulp addition
* generalized usage of `ln_beta`

Version 2.0.0
-------------

* changed rounding modes from records to `R -> Z` functions as arguments
  to the `round` function
  - `rndDN -> Zfloor`
  - `rndUP -> Zceil`
  - `rndZE -> Ztrunc`
  - `rndNE -> ZnearestE`
  - `rndNA -> ZnearestA`
* added typeclasses for automatic inference of properties:
  - `Valid_exp` for `Z -> Z` functions describing formats
  - `Valid_rnd` for `R -> Z` functions describing rounding modes
  - `Exp_not_FTZ` for `Z -> Z` functions describing formats with subnormal
  - `Monotone_exp` for `Z -> Z` functions describing regular formats
  - `Exists_NE` for radix/formats supporting rounding to nearest even
* removed theorems superseded by typeclasses:
  - `FIX_exp_correct`, `FLX_exp_correct`, `FLT_exp_correct`, `FTZ_exp_correct`
  - `FIX_exp_monotone`, `FLX_exp_monotone`, `FLT_monotone`
  - `Rnd_NE_pt_FIX`, `Rnd_NE_pt_FLX`, `Rnd_NE_pt_FLT`
  - `round_NE_pt_FLX`, `round_NE_pt_FLT`
  - `Zrnd_opp_le`, `Zrnd_Z2R_opp`
* removed example file `Fappli_sqrt_FLT_ne.v`
* split theorems on equivalence between specific and generic formats
  into both directions:
  - `FIX_format_generic` and `generic_format_FIX`
  - `FLX_format_generic` and `generic_format_FLX`
  - `FLT_format_generic` and `generic_format_FLT`
  - `FTZ_format_generic` and `generic_format_FTZ`
* modified correctness theorems for IEEE-754 operators so that they also
  mention finiteness of the results
* added a `Flocq_version.Flocq_version` Coq variable for Flocq detection
  and version testing in configure scripts
* moved parts of some files into other files:
  - `Fcore_Raux -> Fcore_Zaux`
  - `Fcalc_digits -> Fcore_digits`
  - `Fappli_IEEE -> Fappli_IEEE_bits`
* renamed functions:
  - `canonic_exponent -> canonic_exp`
  - `digits -> Zdigits`
  - `bounded_prec -> canonic_mantissa`
  - `Bsign_FF -> sign_FF`
  - `shl -> shl_align`
  - `shl_fexp -> shl_align_fexp`
  - `binary_round_sign -> binary_round_aux`
  - `binary_round_sign_shl -> binary_round`
* renamed theorems more uniformly:
  - `Rabs_Rminus_pos -> Rabs_minus_le`
  - `exp_increasing_weak -> exp_le`
  - `ln_beta_monotone -> ln_beta_le`
  - `ln_beta_monotone_abs -> ln_beta_le_abs`
  - `abs_F2R -> F2R_Zabs` (changed direction)
  - `opp_F2R -> F2R_Zopp` (changed direction)
  - `scaled_mantissa_bpow -> scaled_mantissa_mult_bpow`
  - `round_monotone -> round_le`
  - `round_monotone_l -> round_ge_generic`
  - `round_monotone_r -> round_le_generic`
  - `round_monotone_abs_l -> abs_round_ge_generic`
  - `round_monotone_abs_r -> abs_round_le_generic`
  - `generic_format_canonic_exponent -> generic_format_F2R` (modified hypothesis)
  - `canonic_exponent_round -> canonic_exp_round_ge`
  - `generic_N_pt -> round_N_pt`
  - `round_pred_pos_imp_rnd -> round_pred_ge_0`
  - `round_pred_rnd_imp_pos -> round_pred_gt_0`
  - `round_pred_neg_imp_rnd -> round_pred_le_0`
  - `round_pred_rnd_imp_neg -> round_pred_lt_0`
  - `ulp_le_pos -> ulp_le_id`
  - `succ_lt_le -> succ_le_lt`
  - `ulp_monotone -> ulp_le`
  - `ulp_DN_pt_eq -> ulp_DN`
  - `format_pred -> generic_format_pred`
  - `pred_ulp -> pred_plus_ulp`
  - `pred_lt -> pred_lt_id`
  - `FLT_generic_format_FLX -> generic_format_FLT_FLX`
  - `FLX_generic_format_FLT -> generic_format_FLX_FLT`
  - `FIX_generic_format_FLT -> generic_format_FIX_FLT`
  - `FLT_generic_format_FIX -> generic_format_FLT_FIX`
  - `FLT_round_FLX -> round_FLT_FLX`
  - `FTZ_round -> round_FTZ_FLX`
  - `FTZ_round_small -> round_FTZ_small`
  - `FLT_canonic_FLX -> canonic_exp_FLT_FLX`
  - `FLT_canonic_FIX -> canonic_exp_FLT_FIX`
  - `canonic_exponent_opp -> canonic_exp_opp`
  - `canonic_exponent_abs -> canonic_exp_abs`
  - `canonic_exponent_fexp -> canonic_exp_fexp`
  - `canonic_exponent_fexp_pos -> canonic_exp_fexp_pos`
  - `canonic_exponent_DN -> canonic_exp_DN`
  - `canonic_exp_ge -> abs_lt_bpow_prec` (modified hypotheses)
  - `Fopp_F2R -> F2R_opp`
  - `Fabs_F2R -> F2R_abs`
  - `plus_F2R -> F2R_plus`
  - `minus_F2R -> F2R_minus`
  - `mult_F2R -> F2R_mult`
  - `digits_abs -> Zdigits_abs`
  - `digits_ge_0 -> Zdigits_ge_0`
  - `digits_gt_0 -> Zdigits_gt_0`
  - `ln_beta_F2R_Zdigits -> ln_beta_F2R_Zdigits`
  - `digits_shift -> Zdigits_mult_Zpower`
  - `digits_Zpower -> Zdigits_Zpower`
  - `digits_le -> Zdigits_le`
  - `lt_digits -> lt_Zdigits`
  - `Zpower_le_digits -> Zpower_le_Zdigits`
  - `digits_le_Zpower -> Zdigits_le_Zpower`
  - `Zpower_gt_digits -> Zpower_gt_Zdigits`
  - `digits_gt_Zpower -> Zdigits_gt_Zpower`
  - `digits_mult_strong -> Zdigits_mult_strong`
  - `digits_mult -> Zdigits_mult`
  - `digits_mult_ge -> Zdigits_mult_ge`
  - `digits_shr -> Zdigits_div_Zpower`
  - `format_add -> generic_format_plus_prec` (modified hypothesis)
  - `format_nx -> ex_Fexp_canonic`
  - `generic_relative_error -> relative_error`
  - `generic_relative_error_ex -> relative_error_ex`
  - `generic_relative_error_F2R -> relative_error_F2R_emin`
  - `generic_relative_error_F2R_ex -> relative_error_F2R_emin_ex`
  - `generic_relative_error_2 -> relative_error_round`
  - `generic_relative_error_F2R_2 -> relative_error_round_F2R_emin`
  - `generic_relative_error_N -> relative_error_N`
  - `generic_relative_error_N_ex -> relative_error_N_ex`
  - `generic_relative_error_N_F2R -> relative_error_N_F2R_emin`
  - `generic_relative_error_N_F2R_ex -> relative_error_N_F2R_emin_ex`
  - `generic_relative_error_N_2 -> relative_error_N_round`
  - `generic_relative_error_N_F2R_2 -> relative_error_N_round_F2R_emin`
  - `relative_error_FLT_F2R  -> relative_error_FLT_F2R_emin`
  - `relative_error_FLT_F2R_ex -> relative_error_FLT_F2R_emin_ex`
  - `relative_error_N_FLT_2 -> relative_error_N_FLT_round`
  - `relative_error_N_FLT_F2R -> relative_error_N_FLT_F2R_emin`
  - `relative_error_N_FLT_F2R_ex -> relative_error_N_FLT_F2R_emin_ex`
  - `relative_error_N_FLT_F2R_2 -> relative_error_N_FLT_round_F2R_emin`
  - `relative_error_FLX_2 -> relative_error_FLX_round`
  - `relative_error_N_FLX_2 -> relative_error_N_FLX_round`
  - `canonic_bounded_prec -> canonic_canonic_mantissa`
  - `B2R_lt_emax -> abs_B2R_lt_emax`
  - `binary_unicity -> B2FF_inj`
  - `finite_binary_unicity -> B2R_inj`
  - `binary_round_sign_correct -> binary_round_aux_correct`
  - `shl_correct -> shl_align_correct`
  - `snd_shl -> snd_shl_align`
  - `shl_fexp_correct -> shl_align_fexp_correct`
  - `binary_round_sign_shl_correct -> binary_round_correct`

Version 1.4.0
-------------

* improved efficiency of IEEE-754 addition
* fixed compilation with Coq 8.3

Version 1.3
-----------

* fixed overflow handling in IEEE-754 formats with directed rounding

Version 1.2
-----------

* added IEEE-754 binary32 and 64 formats, including infinities and NaN

Version 1.1
-----------

* simplified effective rounding for negative reals
* proved monotonicity of exponent functions for common formats

Version 1.0
-----------

* initial release
