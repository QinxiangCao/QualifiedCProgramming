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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_divexact_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_divexact_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_divexact_entail_wit_1 : mpz_divexact_entail_wit_1.
Proof.
  right.
  intros.
  unfold optional_store_Z.
  Left.
  entailer!.
Qed.

Lemma proof_of_mpz_divexact_entail_wit_2 : mpz_divexact_entail_wit_2.
Proof.
  right.
  intros.
  pose proof (mpz_div_qr_math_exact_quotient 2 zn zd qv_2 rv_2 PreH1 PreH7) as [Hq Hr].
  subst qv_2 rv_2.
  entailer!.
Qed.

Lemma proof_of_mpz_divexact_return_wit_1 : mpz_divexact_return_wit_1.
Proof.
  right.
  intros.
  subst qv rv.
  unfold optional_store_Z.
  Split.
  - Intros_p Hnull. entailer!.
  - Intros_p Hnonnull. entailer!.
Qed.
