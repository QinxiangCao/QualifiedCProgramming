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
From SimpleC.EE.Applications_human.alpha_equiv Require Import subst_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import ast_lib.
Require Import malloc.
Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_subst_var_safety_wit_1 : subst_var_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_subst_var_safety_wit_2 : subst_var_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_subst_var_safety_wit_3 : subst_var_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_subst_var_safety_wit_4 : subst_var_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_1 : subst_var_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_2_pure : subst_var_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_2 : subst_var_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_3 : subst_var_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_4 : subst_var_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_5 : subst_var_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_6_pure : subst_var_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_6 : subst_var_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_7_pure : subst_var_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_7 : subst_var_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_8 : subst_var_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_9 : subst_var_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_10_pure : subst_var_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_10 : subst_var_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_11 : subst_var_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_subst_var_partial_solve_wit_12 : subst_var_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_subst_term_safety_wit_1 : subst_term_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_subst_term_safety_wit_2 : subst_term_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_subst_term_safety_wit_3 : subst_term_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_subst_term_safety_wit_4 : subst_term_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_1 : subst_term_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_2_pure : subst_term_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_2 : subst_term_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_3 : subst_term_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_4_pure : subst_term_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_4 : subst_term_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_5 : subst_term_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_6 : subst_term_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_7_pure : subst_term_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_7 : subst_term_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_8_pure : subst_term_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_8 : subst_term_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_9 : subst_term_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_10 : subst_term_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_11_pure : subst_term_partial_solve_wit_11_pure.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_11 : subst_term_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_12 : subst_term_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_subst_term_partial_solve_wit_13 : subst_term_partial_solve_wit_13.
Proof. Admitted. 

