From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import list_tail_rel_goal.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Require Import glibc_slist_lib.
Require Import list_tail_rel_lib.
Local Open Scope sac.

Lemma proof_of_list_tail_safety_wit_1 : list_tail_safety_wit_1.
Proof. Admitted.

Lemma proof_of_list_tail_safety_wit_2 : list_tail_safety_wit_2.
Proof. Admitted.

Lemma proof_of_list_tail_safety_wit_3 : list_tail_safety_wit_3.
Proof. Admitted.

Lemma proof_of_list_tail_partial_solve_wit_1 : list_tail_partial_solve_wit_1.
Proof. Admitted.

