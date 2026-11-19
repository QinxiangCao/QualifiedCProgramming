Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Psatz.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.stdlib.glibc.horspool_memmem_lib.
(* Dynamic-frontier refinement only; the fixed-length algorithm is unchanged. *)
Require Export SimpleC.EE.stdlib.glibc.horspool_memmem_rel_lib.
Local Open Scope Z_scope.

Definition hp_cstring (bytes : list Z) (hayoff haylen : Z) : Prop :=
  (forall i, 0 <= i < haylen -> Znth (hayoff + i) bytes 0 <> 0) /\
  Znth (hayoff + haylen) bytes 0 = 0.

Definition hp_probe_result (haylen start count result : Z) : Prop :=
  result = Z.min (haylen - start) count.

Lemma hp_probe_bounds : forall total start count result,
  0 <= start <= total -> 0 <= count ->
  hp_probe_result total start count result ->
  0 <= result <= count /\ start + result <= total /\
  (result < count -> start + result = total).
Proof.
  intros total start count result Hstart Hcount Hresult.
  unfold hp_probe_result in Hresult. subst result.
  destruct (Z_le_gt_dec (total - start) count).
  - rewrite Z.min_l by lia. lia.
  - rewrite Z.min_r by lia. lia.
Qed.

Lemma hp_probe_failure : forall total known position needle result,
  0 <= known <= total -> position <= known -> 0 <= needle <= 256 ->
  hp_probe_result total known 2048 result ->
  known + result < position + needle -> known + result = total.
Proof.
  intros. pose proof (hp_probe_bounds total known 2048 result H ltac:(lia) H2).
  intuition lia.
Qed.
