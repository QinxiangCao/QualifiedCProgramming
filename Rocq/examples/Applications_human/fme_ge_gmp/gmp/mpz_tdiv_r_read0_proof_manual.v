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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_proof_manual_part1.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_proof_manual_part2.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_proof_manual_part3.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_proof_manual_part4.

Include mpz_tdiv_r_read0_proof_manual_part1.
Include mpz_tdiv_r_read0_proof_manual_part2.
Include mpz_tdiv_r_read0_proof_manual_part3.
Include mpz_tdiv_r_read0_proof_manual_part4.
