From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_iter_back_2_rel_goal.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Require Import glibc_slist_lib.
Require Import glibc_slist_iter_back_2_rel_lib.
Local Open Scope sac.

Lemma proof_of_glibc_slist_clean_iter_back_2_safety_wit_1 : glibc_slist_clean_iter_back_2_safety_wit_1.
Proof. Admitted.

Lemma proof_of_glibc_slist_clean_iter_back_2_safety_wit_2 : glibc_slist_clean_iter_back_2_safety_wit_2.
Proof. Admitted.

Lemma proof_of_glibc_slist_clean_iter_back_2_safety_wit_3 : glibc_slist_clean_iter_back_2_safety_wit_3.
Proof. Admitted.

Lemma proof_of_glibc_slist_clean_iter_back_2_safety_wit_5 : glibc_slist_clean_iter_back_2_safety_wit_5.
Proof. Admitted.

Lemma proof_of_glibc_slist_clean_iter_back_2_return_wit_2 : glibc_slist_clean_iter_back_2_return_wit_2.
Proof. Admitted.

