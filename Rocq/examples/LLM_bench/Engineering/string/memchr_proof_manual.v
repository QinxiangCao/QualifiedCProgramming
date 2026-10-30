From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Engineering.string Require Import memchr_goal.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Lemma proof_of_memchr_entail_wit_1 : memchr_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_memchr_return_wit_1 : memchr_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold memchr_result.
    right.
    split; [ | reflexivity ].
    assert (i = n_pre) by lia.
    subst i.
    exact PreH10.
Qed.

Lemma proof_of_memchr_return_wit_2 : memchr_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold memchr_result.
    left.
    exists i.
    split; [ lia | ].
    split; [ exact PreH1 | ].
    split; [ exact PreH11 | ].
    rewrite sizeof_char.
    lia.
Qed.
