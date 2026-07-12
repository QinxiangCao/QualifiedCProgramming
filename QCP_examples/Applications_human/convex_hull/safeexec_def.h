/*@ Extern Coq (program :: * => * => *) */
/*@ Extern Coq (unit :: *) */
/*@ Extern Coq (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop)
               (bind: {Sigma} {A} {B} ->  program Sigma A -> (A -> program Sigma B) -> program Sigma B)
               (return : {Sigma} {A} -> A -> program Sigma A) 
               (applyf: {A} {B} -> (A -> B) -> A -> B)
               (equiv: {T} -> T -> T -> Prop)
               (mergesortrec_loc1: list Z -> list Z -> program unit (list Z))
               (mergesortrec_loc2: list Z -> list Z -> program unit (list Z))
               (tt: unit)
               (ATrue: {A} -> A -> Prop)
                */

/*@ Printing Coq Name program := StateRelMonad.M */
/*@ Printing Strategy Name program := StateRelMonad.M */
/*@ Printing Strategy No @ bind */

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib */
/*@ Import Coq Local Open Scope monad */
/*@ Import Coq From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations */
/*@ Import Coq From FP Require Import PartialOrder_Setoid BourbakiWitt */

/*@ include strategies "safeexec.strategies" */
