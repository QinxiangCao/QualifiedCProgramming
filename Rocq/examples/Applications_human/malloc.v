Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

Fixpoint all_zero_list_nat (n: nat) : list Z :=
  match n with
    | O => nil
    | S n0 => 0 :: (all_zero_list_nat n0)
  end.

Definition all_zero_list (n: Z): list Z :=
  all_zero_list_nat (Z.to_nat n).
