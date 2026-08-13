Require Import Coq.Logic.ProofIrrelevance.
(* Require Import Coq.omega.Omega. *)
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.

#[export] Instance Pred_L (A: Type) : Language := Build_Language (A -> Prop).

#[export] Instance Pred_strongGammaP (A: Type): Provable (Pred_L A) :=
  Build_Provable (Pred_L A) (fun x => forall a, x a).

#[export] Instance Pred_strongGammaD (A: Type): Derivable (Pred_L A) :=
  Build_Derivable
    (Pred_L A) (fun Phi x => forall a, (forall y, Phi y -> y a) -> x a).

#[export] Instance Pred_SM (A: Type): Semantics (Pred_L A) (Build_Model A) :=
  Build_Semantics (Pred_L A) (Build_Model A) (fun x => x).
