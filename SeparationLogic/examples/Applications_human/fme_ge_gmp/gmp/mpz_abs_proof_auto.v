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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_abs_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_abs_entail_wit_2_neq : mpz_abs_entail_wit_2_neq.
Proof. Admitted. 

Lemma proof_of_mpz_abs_partial_solve_wit_1_eq_pure : mpz_abs_partial_solve_wit_1_eq_pure.
Proof. Admitted. 

Lemma proof_of_mpz_abs_partial_solve_wit_1_eq : mpz_abs_partial_solve_wit_1_eq.
Proof. Admitted. 

Lemma proof_of_mpz_abs_partial_solve_wit_2_neq : mpz_abs_partial_solve_wit_2_neq.
Proof. Admitted. 

Lemma proof_of_mpz_abs_partial_solve_wit_3_eq : mpz_abs_partial_solve_wit_3_eq.
Proof. Admitted. 

Lemma proof_of_mpz_abs_partial_solve_wit_4_neq : mpz_abs_partial_solve_wit_4_neq.
Proof. Admitted. 

