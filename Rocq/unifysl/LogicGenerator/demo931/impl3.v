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
Definition ASD : Type := Z.
Definition memval : Type := Q * Z.
Definition memlock : Type := Q * option Datatypes.unit * ASD.
Definition heap : Type := addr -> option (memval + memlock).

Definition store_Join := @equiv_Join store.
Definition memval_Join := @prod_Join Q Z Q_Join (@equiv_Join Z).
Definition bool_Join := @option_Join Datatypes.unit (@trivial_Join Datatypes.unit).
Definition QB_Join := @prod_Join Q (option Datatypes.unit) Q_Join bool_Join.
Definition memlock_Join := @prod_Join _ _ QB_Join (@equiv_Join ASD).
Definition mem_Join := @sum_Join memval memlock memval_Join memlock_Join.
Definition heap_Join := @fun_Join addr (option (memval + memlock)) (@option_Join (memval + memlock) mem_Join).
Definition store_Unit := @equiv_Unit store. 
Definition heap_Unit := @fun_Unit addr (option (memval + memlock)) (@option_Unit (memval + memlock)).

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
Definition memval_SA := @prod_SA Q Z Q_Join (@equiv_Join Z) Q_SA (@equiv_SA Z).
Definition bool_SA := @option_SA Datatypes.unit _ (@trivial_SA _).
Definition QB_SA := @prod_SA Q (option Datatypes.unit) Q_Join (bool_Join) Q_SA bool_SA.
Definition memlock_SA := @prod_SA _ _ QB_Join (@equiv_Join ASD) QB_SA (@equiv_SA ASD).
Definition mem_SA := @sum_SA memval memlock memval_Join memlock_Join memval_SA memlock_SA.
Definition heap_SA := @fun_SA addr (option (memval + memlock)) (@option_Join (memval + memlock) mem_Join) (@option_SA (memval + memlock) mem_Join mem_SA).
Definition join_SA := @prod_SA store heap store_Join heap_Join store_SA heap_SA.

Definition store_UJR := @equiv_UJR store.
Definition heap_UJR := @fun_UJR addr (option (memval + memlock)) _ _ (@option_UJR (memval + memlock) mem_Join).
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
