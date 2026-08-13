Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Import ListNotations.

Definition var : Type := nat.
Definition val : Type := Z.
Definition addr : Type := nat.
Definition store : Type := var -> val.
Definition heap : Type := addr -> (option val).
Definition store_Join := @equiv_Join store.
Definition heap_Join := @fun_Join addr (option val) (@option_Join val trivial_Join).
Definition store_Unit := @equiv_Unit store. 
Definition heap_Unit := @fun_Unit addr (option val) (@option_Unit val).

Module NaiveLang.
  Definition model : Type := store * heap.
  Definition join := @prod_Join store heap store_Join heap_Join.
  Definition is_unit := @prod_Unit store heap store_Unit heap_Unit.
  Definition expr := (model -> Prop).
End NaiveLang.

Require Import Interface.

Module NaiveRule.
Include DerivedNames (NaiveLang).

Definition store_SA := @equiv_SA store.
Definition heap_SA := @fun_SA addr (option val) _ (@option_SA val _ trivial_SA).
Definition join_SA := @prod_SA store heap store_Join heap_Join store_SA heap_SA.

Definition store_UJR := @equiv_UJR store.
Definition heap_UJR := @fun_UJR addr (option val) _ _ (@option_UJR val trivial_Join).
Definition state_UJR := @prod_UJR store heap store_Unit heap_Unit store_Join heap_Join store_UJR heap_UJR.

Lemma join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m) .
Proof.
  pose proof join_SA. induction H. apply join_comm.
Qed.

Lemma join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz) .
Proof.
  pose proof join_SA. induction H. tauto.
Qed.

End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
(* Module Solver := IPSolver NaiveLang. *)
Import T.
(* Import Solver. *)
