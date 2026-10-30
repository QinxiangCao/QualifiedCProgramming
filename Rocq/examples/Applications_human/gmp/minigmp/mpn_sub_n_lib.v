Require Export SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.


Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Psatz.
Lemma limb_sub_step__alias_ap : (forall a b c u v,
  0 <= a < UINT_MOD -> 0 <= b < UINT_MOD -> 0 <= c <= 2 ->
  (u = 0 /\ c <= IntLib.unsigned_last_nbits (b+c) 32 \/
   u = 1 /\ IntLib.unsigned_last_nbits (b+c) 32 < c) ->
  (v = 0 /\ IntLib.unsigned_last_nbits (b+c) 32 <= a \/
   v = 1 /\ a < IntLib.unsigned_last_nbits (b+c) 32) ->
  0 <= IntLib.unsigned_last_nbits (a-IntLib.unsigned_last_nbits (b+c) 32) 32 < UINT_MOD /\
  IntLib.unsigned_last_nbits (a-IntLib.unsigned_last_nbits (b+c) 32) 32 - (u+v)*UINT_MOD = a-b-c)%Z.
Proof.
  Local Open Scope Z_scope.
  intros a b c u v Ha Hb Hc Hu Hv.
  unfold IntLib.unsigned_last_nbits in *.
  change (2^32) with UINT_MOD in *.
  assert (Ht : 0 <= (b+c) mod UINT_MOD < UINT_MOD) by (apply Z.mod_pos_bound; exact UINT_MOD_pos).
  assert (He : (b+c) mod UINT_MOD = b+c-u*UINT_MOD).
  { destruct (Z_lt_ge_dec (b+c) UINT_MOD) as [Hlo|Hhi].
    - rewrite Z.mod_small in * by lia. destruct Hu as [[-> ?]|[-> ?]]; lia.
    - assert (E : (b+c) mod UINT_MOD = b+c-UINT_MOD).
      { replace (b+c) with ((b+c-UINT_MOD)+1*UINT_MOD) at 1 by ring.
        rewrite Z.mod_add by (pose proof UINT_MOD_pos; lia).
        apply Z.mod_small. unfold UINT_MOD in *; lia. }
      rewrite E in *. destruct Hu as [[-> ?]|[-> ?]]; unfold UINT_MOD in *; lia. }
  split; [apply Z.mod_pos_bound; exact UINT_MOD_pos|].
  destruct Hv as [[-> Hv]|[-> Hv]].
  - rewrite Z.mod_small by lia. lia.
  - assert (E : (a - (b+c) mod UINT_MOD) mod UINT_MOD = a - (b+c) mod UINT_MOD + UINT_MOD).
    { replace (a - (b+c) mod UINT_MOD) with
        ((a - (b+c) mod UINT_MOD + UINT_MOD) + (-1)*UINT_MOD) at 1 by ring.
      rewrite Z.mod_add by (pose proof UINT_MOD_pos; lia).
      apply Z.mod_small; lia. }
    rewrite E. lia.
Qed.
Lemma prefix_sub_step__alias_ap : (forall A B R i c r cnew,
  0 <= i < Zlength A -> Zlength A = Zlength B -> Zlength R = i ->
  list_within_bound UINT_MOD A -> list_within_bound UINT_MOD B ->
  list_to_Z UINT_MOD R-c*UINT_MOD^i =
    list_to_Z UINT_MOD (Positional.sublist 0 i A)-list_to_Z UINT_MOD (Positional.sublist 0 i B) ->
  r-cnew*UINT_MOD = Positional.Znth i A 0-Positional.Znth i B 0-c ->
  list_to_Z UINT_MOD (List.app R (r::nil))-cnew*UINT_MOD^(i+1) =
    list_to_Z UINT_MOD (Positional.sublist 0 (i+1) A)-list_to_Z UINT_MOD (Positional.sublist 0 (i+1) B))%Z.
Proof.
  Local Open Scope Z_scope.
  intros A B R i c r cnew Hi Hlen HR HA HB Hinv Hstep.
  rewrite list_to_Z_app by exact UINT_MOD_pos.
  rewrite list_to_Z_single, HR.
  rewrite !list_to_Z_list_append by (try exact UINT_MOD_pos; try assumption; lia).
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r. nia.
Qed.
