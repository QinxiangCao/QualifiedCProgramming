Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Engineering.string Require Import memchr_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Lemma proof_of_memchr_entail_wit_1 : memchr_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_memchr_return_wit_1 : memchr_return_wit_1.
Proof.
  pre_process.
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
  pre_process.
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
