Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import String.
Require Import Permutation.

From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From compcert.lib Require Export Integers.

From SimpleC.SL Require Import Mem.
From SimpleC.SL Require Export IntLib.
From AUXLib Require Export ListLib.
From SimpleC.SL Require Export CommonAssertion.

Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.

(** The real definition of assertion :
Record state := {
  Mem : mem;
}.

Coercion Mem : state >-> mem. 

Definition assertion : Type := state -> Prop. 

To simplify the proof, we write as the following.
*)

Module Type SL <: SeparationLogicSig.

(* Modle Names: LanguageSig. *)

  Definition model : Type := mem.

  Definition expr := model -> Prop .

  Definition join : model -> model -> model -> Prop := mem_join.
  
  Definition is_unit : model -> Prop := mem_empty.

(* End LanguageSig. *)

Include DerivedNamesSig.

(* LogicRule <: PrimitiveRuleSig Names *)

  Theorem unit_join : (forall n : model, exists u : model, is_unit u /\ join n u n) .
  Proof.
    intros. exists empty_mem.
    unfold is_unit , join.
    split ; solve_empmem.
  Qed.
      
  Theorem unit_spec : (forall n m u : model, is_unit u -> join n u m -> n = m) .
  Proof.
    intros. unfold is_unit, join in *.
    solve_empmem. auto. 
  Qed.

  Definition join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m) := mem_join_comm.

  Definition join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz) := mem_join_assoc2.  

(* End Rules. *)

Include LogicTheoremSig'.

Arguments exp {A}.

(* The following are basic definitions *)

Definition mstore (p: addr) (v: Z): expr := 
  fun st =>
    exists v', Byte.eqm v v' /\ st = single_byte_mem p v'.

Definition mstore_noninit (p: addr): expr :=
  fun st => ((st = single_Noninit_mem p) \/ (exists v, st = single_byte_mem p v)).

Theorem mstore_mstore_noninit:
  forall p v s,
    mstore p v s ->
    mstore_noninit p s.
Proof.
  unfold mstore, mstore_noninit.
  intros.
  right.
  destruct H as [v' ?]; exists v'.
  tauto.
Qed.

Theorem mstore_eqm: forall p v v',
  Byte.eqm v v' ->
  derivable1 (mstore p v) (mstore p v').
Proof.
  intros.
  unfold mstore, derivable1.
  intros m [v'' [? ?] ].
  exists v''.
  split; [| tauto].
  eapply Byte.eqm_trans.
  + apply Byte.eqm_sym, H.
  + apply H0.
Qed.

Theorem dup_mstore_noninit: 
  forall x,
    derivable1
      (sepcon (mstore_noninit x) (mstore_noninit x))
      (coq_prop False).
Proof.
  unfold mstore_noninit, sepcon, derivable1.
  intros.
  destruct H as [m1 [m2 [? [Hm1 Hm2]]]].
  unfold join, mem_join in H.
  specialize (H x).
  destruct H as [ | [ | [ | [ | ]]]].
  + destruct H as [? [? ?]].
    destruct Hm1.
    - rewrite H2 in H.
      unfold single_Noninit_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
    - destruct H2 as [v ?].
      rewrite H2 in H.
      unfold single_byte_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
  + destruct H as [? [? ?]].
    destruct Hm1.
    - rewrite H2 in H.
      unfold single_Noninit_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
    - destruct H2 as [v ?].
      rewrite H2 in H.
      unfold single_byte_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
  + destruct H as [? [? ?]].
    destruct Hm2.
    - rewrite H2 in H0.
      unfold single_Noninit_mem in H0.
      rewrite Z.eqb_refl in H0.
      discriminate.
    - destruct H2 as [v ?].
      rewrite H2 in H0.
      unfold single_byte_mem in H0.
      rewrite Z.eqb_refl in H0.
      discriminate.
  + destruct H as [v' [? [? ?]]].
    destruct Hm1.
    - rewrite H2 in H.
      unfold single_Noninit_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
    - destruct H2 as [v ?].
      rewrite H2 in H.
      unfold single_byte_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
  + destruct H as [v' [? [? ?]]].
  destruct Hm2.
  - rewrite H2 in H0.
    unfold single_Noninit_mem in H0.
    rewrite Z.eqb_refl in H0.
    discriminate.
  - destruct H2 as [v ?].
    rewrite H2 in H0.
    unfold single_byte_mem in H0.
    rewrite Z.eqb_refl in H0.
    discriminate.
Qed.

End SL.

