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
From SimpleC.EE.QCP_demos_human Require Import sll_lib.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition store_queue (x: addr) (l: list Z): Assertion :=
  EX (p1 p2: addr) (l1 l2: list Z),
    “ l = l1 ++ rev l2 ” &&
    &(x # "queue" ->ₛ "l1") # Ptr |-> p1 **
    &(x # "queue" ->ₛ "l2") # Ptr |-> p2 **
    sll p1 l1 ** sll p2 l2.

