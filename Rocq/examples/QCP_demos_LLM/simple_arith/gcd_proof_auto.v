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
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import gcd_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_gcd_safety_wit_1 : gcd_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_gcd_safety_wit_2 : gcd_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_gcd_entail_wit_1 : gcd_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_gcd_partial_solve_wit_1_pure : gcd_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_gcd_partial_solve_wit_1 : gcd_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_gcd_partial_solve_wit_2 : gcd_partial_solve_wit_2.
Proof. Admitted. 

