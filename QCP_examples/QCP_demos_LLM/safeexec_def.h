/*@ Import Lean import MonadLib.StateRelMonad.safeexec_lib */
/*@ Import Lean open MonadLib MonadLib.StateRelMonad */
/*@ Printing Lean Name program := MonadLib.StateRelMonad.M */
/*@ Extern Coq (program :: * => * => *) */
/*@ Extern Coq (unit :: *) */
/*@ Extern Coq (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop)
               (bind: {Sigma} {A} {B} ->  program Sigma A -> (A -> program Sigma B) -> program Sigma B)
               (return : {Sigma} {A} -> A -> program Sigma A) 
               (applyf: {A} {B} -> (A -> B) -> A -> B)
               (tt: unit)
               (ATrue: {A} -> A -> Prop)
                */

/*@ Printing Coq Name program := StateRelMonad.M */
/*@ Printing Strategy Name program := StateRelMonad.M */
/*@ Printing Strategy No @ bind */

/*@ Import Coq From MonadLib Require Export MonadLib */
/*@ Import Coq From MonadLib.StateRelMonad Require Export StateRelMonad */
/*@ Import Coq Export MonadNotation */
/*@ Import Coq Local Open Scope monad */
/*@ Import Coq From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations */
/*@ Import Coq From FP Require Import PartialOrder_Setoid BourbakiWitt */

/*@ include strategies "safeexec.strategies" */
