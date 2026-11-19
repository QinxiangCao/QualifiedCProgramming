From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.EE.stdlib.musl Require Import strstr_rel_cleanup_strategy_goal.
Import naive_C_Rules64.
Local Open Scope sac.

Lemma strstr_rel_cleanup_strategy1_correctness : strstr_rel_cleanup_strategy1.
Proof.
  pre_process_default.
  apply UInt64Array.mixed_full_to_undef_full.
Qed.

Lemma strstr_rel_cleanup_strategy2_correctness : strstr_rel_cleanup_strategy2.
Proof.
  pre_process_default.
  change (StoreUInt64AsElement.storeA p 0 v **
          UInt64Array.undef_seg p 1 n |-- UInt64Array.undef_full p n).
  sep_apply (StoreUInt64AsElement.store_to_undefstore p 0 v).
  rewrite <- (UInt64Array.undef_seg_unfold p 0 n) by lia.
  sep_apply UInt64Array.undef_seg_to_undef_full.
  replace (p + 0 * sizeof(UINT64)) with p by lia.
  replace (n - 0) with n by lia.
  cancel.
Qed.
