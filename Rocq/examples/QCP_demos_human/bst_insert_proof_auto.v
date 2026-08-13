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
From SimpleC.EE.QCP_demos_human Require Import bst_insert_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.bst_lib.
Import get_right_most.
Local Open Scope sac.

Lemma proof_of_insert_safety_wit_1 : insert_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_insert_safety_wit_2 : insert_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_insert_safety_wit_3 : insert_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_insert_safety_wit_4 : insert_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_insert_partial_solve_wit_2_pure : insert_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_insert_partial_solve_wit_2 : insert_partial_solve_wit_2.
Proof. Admitted. 

