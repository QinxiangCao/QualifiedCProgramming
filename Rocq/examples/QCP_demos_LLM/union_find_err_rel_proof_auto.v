Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import union_find_err_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_LLM.union_find_err_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_uf_find_c_entail_wit_3 : uf_find_c_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_uf_find_c_return_wit_1 : uf_find_c_return_wit_1.
Proof. Admitted. 

Lemma proof_of_uf_find_c_partial_solve_wit_1 : uf_find_c_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_uf_find_c_partial_solve_wit_2_pure : uf_find_c_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_uf_find_c_partial_solve_wit_2 : uf_find_c_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_uf_find_c_partial_solve_wit_3 : uf_find_c_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_uf_union_c_safety_wit_1 : uf_union_c_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_uf_union_c_safety_wit_2 : uf_union_c_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_uf_union_c_entail_wit_2 : uf_union_c_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_uf_union_c_entail_wit_3 : uf_union_c_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_uf_union_c_return_wit_1 : uf_union_c_return_wit_1.
Proof. Admitted. 

Lemma proof_of_uf_union_c_return_wit_2 : uf_union_c_return_wit_2.
Proof. Admitted. 

Lemma proof_of_uf_union_c_return_wit_3 : uf_union_c_return_wit_3.
Proof. Admitted. 

Lemma proof_of_uf_union_c_return_wit_4 : uf_union_c_return_wit_4.
Proof. Admitted. 

Lemma proof_of_uf_union_c_partial_solve_wit_1_pure : uf_union_c_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_uf_union_c_partial_solve_wit_1 : uf_union_c_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_uf_union_c_partial_solve_wit_2 : uf_union_c_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_uf_union_c_partial_solve_wit_3 : uf_union_c_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_uf_union_c_partial_solve_wit_4 : uf_union_c_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_uf_union_c_partial_solve_wit_5 : uf_union_c_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_uf_union_c_partial_solve_wit_6 : uf_union_c_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_uf_union_c_partial_solve_wit_7 : uf_union_c_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_uf_union_c_partial_solve_wit_8 : uf_union_c_partial_solve_wit_8.
Proof. Admitted. 

