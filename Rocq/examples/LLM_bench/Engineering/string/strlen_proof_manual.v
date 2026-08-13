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
From SimpleC.EE.LLM_bench.Engineering.string Require Import strlen_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Lemma proof_of_strlen_entail_wit_1 : strlen_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel (store_string s_pre str).
  - split_pures.
    + dump_pre_spatial; auto.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; unfold string_length; apply Zlength_nonneg.
    + dump_pre_spatial; intros k Hk; lia.
Qed.

Lemma proof_of_strlen_entail_wit_2 : strlen_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_lt : i < string_length str).
  { eapply c_string_nonzero_index_lt; eauto. }
  split_pure_spatial.
  - unfold store_string; cancel.
  - split_pures.
    + dump_pre_spatial; auto.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial.
      intros k Hk.
      destruct (Z.eq_dec k i) as [Heq | Hneq].
      * subst k.
        unfold c_string in PreH1.
        rewrite app_Znth1 in PreH1 by
          (unfold string_length in Hi_lt; lia).
        exact PreH1.
      * apply PreH6; lia.
Qed.

Lemma proof_of_strlen_return_wit_1 : strlen_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - unfold store_string; cancel.
  - dump_pre_spatial.
    unfold string_length in *.
    unfold c_string in PreH1.
    destruct PreH2 as [_ Hno].
    destruct (Z_lt_ge_dec i (Zlength str)) as [Hi | Hi].
    + rewrite app_Znth1 in PreH1 by lia.
      specialize (Hno i ltac:(lia)).
      contradiction.
    + lia.
Qed.
