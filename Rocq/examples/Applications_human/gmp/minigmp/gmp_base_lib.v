Require Export SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.


Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Psatz.
Lemma half_product_mod__umul_product : forall a b : Z,
  (0 <= a < 65536 -> 0 <= b < 65536 ->
  (a * b) mod 4294967296 = a * b)%Z.
Proof.
  intros a b Ha Hb.
  apply Z.mod_small. nia.
Qed.
Lemma mul_prefix_step__mul_transition : (forall (l r : list Z) (N i v c p h : Z),
  Zlength l = N -> Zlength r = i -> 0 <= i < N ->
  list_within_bound UINT_MOD l -> list_within_bound UINT_MOD r ->
  0 <= v < UINT_MOD -> 0 <= c < UINT_MOD ->
  0 <= p < UINT_MOD -> 0 <= h < UINT_MOD ->
  list_to_Z UINT_MOD r + c * UINT_MOD ^ i =
    list_to_Z UINT_MOD (ListLib.Base.Positional.sublist 0 i l) * v ->
  h * UINT_MOD + p = ListLib.Base.Positional.Znth i l 0 * v ->
  let s := (p+c) mod UINT_MOD in
  let k := h + (if Z_lt_dec s c then 1 else 0) in
  0 <= k < UINT_MOD /\
  list_within_bound UINT_MOD (r ++ s :: nil) /\
  list_to_Z UINT_MOD (r ++ s :: nil) + k * UINT_MOD ^ (i+1) =
    list_to_Z UINT_MOD (ListLib.Base.Positional.sublist 0 (i+1) l) * v)%Z.
Proof.
  intros l r N i v c p h Hl Hr Hi Hdl Hdr Hv Hc Hp Hh Heq Hprod s k.
  assert (HB : (0 < UINT_MOD)%Z) by (unfold UINT_MOD; lia).
  pose proof (list_within_bound_Znth_bound UINT_MOD l i ltac:(lia) Hdl) as Hd.
  assert (Hmax : (h <= UINT_MOD-2)%Z).
  { unfold UINT_MOD in *; nia. }
  assert (Hs : (0 <= s < UINT_MOD)%Z).
  { unfold s; apply Z.mod_pos_bound; exact HB. }
  assert (Hcarry : (p+c = s + (if Z_lt_dec s c then 1 else 0)*UINT_MOD)%Z).
  { destruct (Z_lt_dec s c) as [Hlt|Hge].
    - pose proof (Z_mod_add_carry p c UINT_MOD ltac:(lia) Hp Hc Hlt); lia.
    - pose proof (Z_mod_add_uncarry p c UINT_MOD ltac:(lia) Hp Hc ltac:(lia)); lia. }
  split.
  { unfold k; destruct (Z_lt_dec s c); lia. }
  split.
  { apply list_within_bound_app_single; assumption. }
  rewrite (list_to_Z_concat_r UINT_MOD HB r s Hs), Hr.
  rewrite (list_to_Z_list_append UINT_MOD HB l i ltac:(lia) Hdl).
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  unfold k.
  nia.
Qed.
