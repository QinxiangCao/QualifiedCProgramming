#ifndef KOSARAJU_SAFEEXECE_DEF_H
#define KOSARAJU_SAFEEXECE_DEF_H

/*@ Extern Coq (program :: * => * => *) */
/*@ Extern Coq (unit :: *) */
/*@ Extern Coq (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop)
               (return : {Sigma} {A} -> A -> program Sigma A) 
               (bind: {Sigma} {A} {B} ->  program Sigma A -> (A -> program Sigma B) -> program Sigma B)
               (applyf: {A} {B} -> (A -> B) -> A -> B)
               (tt: unit)
               (ATrue: {A} -> A -> Prop)
               */

/*@ Printing Coq Name program := MonadErr.M */
/*@ Printing Strategy Name program := MonadErr.M */
/*@ Printing Strategy No @ bind */

/*@ Import Coq From MonadLib Require Export MonadLib */
/*@ Import Coq From MonadLib.MonadErr Require Export StateRelMonadErr */
/*@ Import Coq Export MonadNotation */
/*@ Import Coq Local Open Scope monad */
/*@ Import Coq From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations */
/*@ Import Coq From FP Require Import PartialOrder_Setoid BourbakiWitt */

/*@ include strategies "safeexecE.strategies" */

#endif
