Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition store_int_pair_x_only (p: addr) (x: Z): Assertion :=
  &(p # "int_pair" ->ₛ "a") # Int |-> x.

Definition store_int_pair_y_only (p: addr) (y: Z): Assertion :=
  &(p # "int_pair" ->ₛ "b") # Int |-> y.
