Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Psatz.
From SimpleC.EE.stdlib.glibc Require Export two_way_rel_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.

Definition tw_terminator (base total : Z) : Assertion :=
  ((base + total) # UChar |-> 0).

Definition tw_nonzero_bytes (bytes : list Z) : Prop :=
  Forall (fun b => b <> 0) bytes.

(* strnlen's mathematical result; the NUL is at absolute offset total. *)
Definition tw_probe_result (total known budget result : Z) : Prop :=
  result = Z.min (total - known) budget.

Lemma tw_probe_bounds : forall total known budget result,
  0 <= known <= total -> 0 <= budget ->
  tw_probe_result total known budget result ->
  0 <= result /\ known + result <= total /\
  (result < budget -> known + result = total).
Proof.
  unfold tw_probe_result; intros; subst result.
  destruct (Z_le_dec (total-known) budget).
  - rewrite Z.min_l by lia; lia.
  - rewrite Z.min_r by lia; lia.
Qed.

(* A full-budget probe covers the requested window. Thus failure really
   means the logical search bound failed, not merely that a prefix ran out. *)
Lemma tw_probe_available : forall total known pos len result,
  0 <= known <= total -> 0 <= pos <= known -> 0 < len ->
  tw_probe_result total known (len + 512) result ->
  (pos + len <= known + result <-> pos + len <= total).
Proof.
  unfold tw_probe_result; intros; subst result.
  destruct (Z_le_dec (total-known) (len+512)).
  - rewrite Z.min_l by lia; lia.
  - rewrite Z.min_r by lia; lia.
Qed.

Lemma tw_shift_table_bound : forall patn table c,
  shift_table_build_prefix patn (Zlength patn) table ->
  0 <= c < 256 -> 0 <= Znth c table 0 <= Zlength patn.
Proof.
  intros patn table c [Hu [Ht Hentry]] Hc.
  destruct (Hentry c Hc) as [[idx [Hocc Heq]] | [Habs Heq]];
    rewrite Heq; [unfold last_occ_before in Hocc |]; lia.
Qed.
