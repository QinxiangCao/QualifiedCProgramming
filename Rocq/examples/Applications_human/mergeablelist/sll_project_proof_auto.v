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
From SimpleC.EE.Applications_human.mergeablelist Require Import sll_project_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.mergeablelist.sll_project_lib.
Local Open Scope sac.

Lemma proof_of_nil_list_safety_wit_1 : nil_list_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_nil_list_return_wit_1 : nil_list_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cons_list_partial_solve_wit_1 : cons_list_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_free_list_entail_wit_1 : free_list_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_free_list_entail_wit_2 : free_list_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_free_list_partial_solve_wit_1_pure : free_list_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_free_list_partial_solve_wit_1 : free_list_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_free_list_partial_solve_wit_2 : free_list_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_map_list_safety_wit_1 : map_list_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_map_list_partial_solve_wit_1_pure : map_list_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_map_list_partial_solve_wit_1 : map_list_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_nil_list_box_return_wit_1 : nil_list_box_return_wit_1.
Proof. Admitted. 

Lemma proof_of_nil_list_box_partial_solve_wit_1 : nil_list_box_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_nil_list_box_partial_solve_wit_2 : nil_list_box_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cons_list_box_safety_wit_1 : cons_list_box_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cons_list_box_safety_wit_2 : cons_list_box_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cons_list_box_safety_wit_3 : cons_list_box_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cons_list_box_safety_wit_4 : cons_list_box_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cons_list_box_partial_solve_wit_1 : cons_list_box_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cons_list_box_partial_solve_wit_2 : cons_list_box_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cons_list_box_partial_solve_wit_3 : cons_list_box_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_cons_list_box_partial_solve_wit_4 : cons_list_box_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_map_list_box_return_wit_1 : map_list_box_return_wit_1.
Proof. Admitted. 

Lemma proof_of_map_list_box_partial_solve_wit_1 : map_list_box_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_map_list_box_partial_solve_wit_2 : map_list_box_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_map_list_box_which_implies_wit_1 : map_list_box_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_free_list_box_return_wit_1 : free_list_box_return_wit_1.
Proof. Admitted. 

Lemma proof_of_free_list_box_partial_solve_wit_1 : free_list_box_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_free_list_box_partial_solve_wit_2 : free_list_box_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_free_list_box_partial_solve_wit_3 : free_list_box_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_free_list_box_which_implies_wit_1 : free_list_box_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_app_list_box_safety_wit_1 : app_list_box_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_app_list_box_partial_solve_wit_1 : app_list_box_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_app_list_box_partial_solve_wit_2 : app_list_box_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_app_list_box_partial_solve_wit_3 : app_list_box_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_sll_length_safety_wit_1 : sll_length_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_length_partial_solve_wit_1_pure : sll_length_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_sll_length_partial_solve_wit_1 : sll_length_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_sll2array_safety_wit_1 : sll2array_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_sll2array_safety_wit_2 : sll2array_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_sll2array_partial_solve_wit_1_pure : sll2array_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_sll2array_partial_solve_wit_1 : sll2array_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_sll2array_partial_solve_wit_2_pure : sll2array_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_sll2array_partial_solve_wit_2 : sll2array_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_sll2array_partial_solve_wit_3 : sll2array_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_sll2array_partial_solve_wit_4 : sll2array_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_sllb2array_return_wit_1 : sllb2array_return_wit_1.
Proof. Admitted. 

Lemma proof_of_sllb2array_partial_solve_wit_1 : sllb2array_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_sllb2array_partial_solve_wit_2_pure : sllb2array_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_sllb2array_partial_solve_wit_2 : sllb2array_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_sllb2array_which_implies_wit_1 : sllb2array_which_implies_wit_1.
Proof. Admitted. 

