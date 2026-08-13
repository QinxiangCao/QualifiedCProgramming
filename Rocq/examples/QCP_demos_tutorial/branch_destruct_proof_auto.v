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
From SimpleC.EE.QCP_demos_tutorial Require Import branch_destruct_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_example_safety_wit_1 : example_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_example_safety_wit_2_Less : example_safety_wit_2_Less.
Proof. Admitted. 

Lemma proof_of_example_safety_wit_3_Less25 : example_safety_wit_3_Less25.
Proof. Admitted. 

Lemma proof_of_example_safety_wit_4_Less50 : example_safety_wit_4_Less50.
Proof. Admitted. 

Lemma proof_of_example_safety_wit_5_Eq : example_safety_wit_5_Eq.
Proof. Admitted. 

Lemma proof_of_example_safety_wit_6_Greater : example_safety_wit_6_Greater.
Proof. Admitted. 

Lemma proof_of_example_return_wit_1_Less25 : example_return_wit_1_Less25.
Proof. Admitted. 

Lemma proof_of_example_return_wit_2_Less50 : example_return_wit_2_Less50.
Proof. Admitted. 

Lemma proof_of_example_return_wit_3_Eq : example_return_wit_3_Eq.
Proof. Admitted. 

Lemma proof_of_example_return_wit_4_Greater : example_return_wit_4_Greater.
Proof. Admitted. 

