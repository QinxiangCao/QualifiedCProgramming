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
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.

Import naive_C_Rules.
Local Open Scope sac.

Definition store_queue (x: addr) (l: list Z): Assertion :=
  EX (h t: addr) (u: Z) (v: addr),
    “ t <> 0 ” &&
    &(x # "queue" ->ₛ "head") # Ptr |-> h **
    &(x # "queue" ->ₛ "tail") # Ptr |-> t **
    sllseg h t l **
    &(t # "list" ->ₛ "data") # Int |-> u **
    &(t # "list" ->ₛ "next") # Ptr |-> v.
