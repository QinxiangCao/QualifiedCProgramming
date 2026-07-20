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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import solve_basis_into_col_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import solve_basis_into_col_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_solve_basis_into_col_gmp_return_wit_1 : solve_basis_into_col_gmp_return_wit_1.
Proof.
  unfold solve_basis_into_col_gmp_return_wit_1.
  right.
  intros.
  match goal with
  | H : gauss_success _ _ _ X |- _ =>
      destruct H as [Hvec Hsol]
  end.
  Exists (matrix_set_col B_low_level_spec col_pre X).
  entailer!.
  eapply inverse_cols_prefix_spec_extend; eauto; lia.
Qed.
