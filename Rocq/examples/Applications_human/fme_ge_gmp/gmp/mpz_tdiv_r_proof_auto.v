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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_tdiv_r_safety_wit_1 : mpz_tdiv_r_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_tdiv_r_safety_wit_2 : mpz_tdiv_r_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_tdiv_r_partial_solve_wit_1_pure : mpz_tdiv_r_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_mpz_tdiv_r_partial_solve_wit_1 : mpz_tdiv_r_partial_solve_wit_1.
Proof. Admitted. 

