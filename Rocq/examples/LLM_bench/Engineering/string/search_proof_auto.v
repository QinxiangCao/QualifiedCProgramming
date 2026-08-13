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
From SimpleC.EE.LLM_bench.Engineering.string Require Import search_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Lemma proof_of_memchr_safety_wit_1 : memchr_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_memchr_safety_wit_2 : memchr_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_memchr_safety_wit_3 : memchr_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_memchr_entail_wit_2 : memchr_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_memchr_partial_solve_wit_1 : memchr_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_strchr_safety_wit_1 : strchr_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_strchr_safety_wit_2 : strchr_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_strchr_safety_wit_3 : strchr_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_strchr_safety_wit_4 : strchr_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_strchr_safety_wit_5 : strchr_safety_wit_5.
Proof. Admitted. 

