Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import ZArith.
Require Import QArith.
Require Import Lqa.
Import ListNotations.

Definition Q_Join := fun q1 q2 q => 
  0 <= q1 /\ 0 <= q2 /\ 0 <= q /\ q1 <= 1 /\ q2 <= 1 /\ q <= 1 /\ Qeq q (q1 + q2).
Definition Q_SA : @SeparationAlgebra Q Q_Join.
Proof.
  constructor; intros; unfold join, Q_Join in *;
  [| exists (mxyz - mx)]; repeat (split; try tauto; lra).
Qed.

Definition var : Type := nat.
Definition val : Type := Z.
Definition addr : Type := nat.
Definition store : Type := var -> val.
Definition heap : Type := addr -> option (Q * val).
Definition store_Join := @equiv_Join store.
Definition QV_Join := @prod_Join Q val Q_Join equiv_Join.
Definition heap_Join := @fun_Join addr (option (Q * val)) (@option_Join (Q*val) QV_Join).
Definition store_Unit := @equiv_Unit store. 
Definition heap_Unit := @fun_Unit addr (option (Q * val)) (@option_Unit (Q*val)).

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

Definition QV_SA := @prod_SA Q val Q_Join _ Q_SA (@equiv_SA val).
Definition heap_SA := @fun_SA addr (option (Q * val)) (@option_Join (Q*val) QV_Join) (@option_SA (Q * val) QV_Join QV_SA).
Definition join_SA := @prod_SA store heap store_Join heap_Join store_SA heap_SA.

Definition store_UJR := @equiv_UJR store.
Definition heap_UJR := @fun_UJR addr (option (Q*val)) _ _ (@option_UJR (Q*val) QV_Join).
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
