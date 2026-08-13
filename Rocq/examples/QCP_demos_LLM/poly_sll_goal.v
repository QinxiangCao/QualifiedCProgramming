Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.poly_sll_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import poly_sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import poly_sll_strategy_proof.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (A: Type) (p_pre: Z) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll storeA p_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_entail_wit_1 := 
forall (A: Type) (p_pre: Z) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) ,
  (sll storeA p_pre l )
|--
  “ (0 = 0) ” 
  &&  “ (p_pre = p_pre) ”
  &&  (sll storeA 0 (@nil A) )
  **  (sll storeA p_pre l )
.

Definition reverse_entail_wit_2 := 
(
forall (A: Type) (p_pre: Z) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (w: Z) (v: Z) (PreH1 : (w = 0)) (PreH2 : (v = p_pre)) ,
  (sll storeA w (@nil A) )
  **  (sll storeA v l )
|--
  EX (l1: (@list A))  (l2: (@list A)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll storeA w l1 )
  **  (sll storeA v l2 )
) \/
(
forall (A: Type) (p_pre: Z) (l: (@list A)) (w: Z) (v: Z) (PreH1 : (w = 0)) (PreH2 : (v = p_pre)) ,
  TT && emp 
|--
  “ (l = (app ((rev ((@nil A)))) (l))) ”
  &&  emp
).

Definition reverse_entail_wit_2_split_goal_1 := 
forall (A: Type) (p_pre: Z) (l: (@list A)) (w: Z) (v: Z) (PreH1 : (w = 0)) (PreH2 : (v = p_pre)) ,
  (l = (app ((rev ((@nil A)))) (l)))
.

Definition reverse_entail_wit_3 := 
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (w: Z) (l1_2: (@list A)) (l2_2: (@list A)) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) ,
  (sll storeA w l1_2 )
  **  (sll storeA v l2_2 )
|--
  EX (vnext: Z)  (vdata: Z)  (x: A)  (xs: (@list A))  (l1: (@list A))  (l2: (@list A)) ,
  “ (l = (app ((rev (l1))) (l2))) ” 
  &&  “ (v <> 0) ” 
  &&  “ (l2 = (cons (x) (xs))) ”
  &&  (sll storeA w l1 )
  **  ((&((v)  # "list" ->ₛ "data")) # Ptr  |-> vdata)
  **  (storeA vdata x )
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> vnext)
  **  (sll storeA vnext xs )
.

Definition reverse_entail_wit_4 := 
(
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (l1_2: (@list A)) (l2_2: (@list A)) (x: A) (xs: (@list A)) (vnext: Z) (vdata: Z) (v: Z) (w: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (x) (xs)))) ,
  (sll storeA w l1_2 )
  **  ((&((v)  # "list" ->ₛ "data")) # Ptr  |-> vdata)
  **  (storeA vdata x )
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll storeA vnext xs )
|--
  EX (l1: (@list A))  (l2: (@list A)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll storeA v l1 )
  **  (sll storeA vnext l2 )
) \/
(
forall (A: Type) (l: (@list A)) (l1_2: (@list A)) (l2_2: (@list A)) (x: A) (xs: (@list A)) (v: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (x) (xs)))) ,
  TT && emp 
|--
  “ (l = (app ((rev ((cons (x) (l1_2))))) (xs))) ”
  &&  emp
).

Definition reverse_entail_wit_4_split_goal_1 := 
forall (A: Type) (l: (@list A)) (l1_2: (@list A)) (l2_2: (@list A)) (x: A) (xs: (@list A)) (v: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (x) (xs)))) ,
  (l = (app ((rev ((cons (x) (l1_2))))) (xs)))
.

Definition reverse_return_wit_1 := 
(
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (w: Z) (l1: (@list A)) (l2: (@list A)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll storeA w l1 )
  **  (sll storeA v l2 )
|--
  (sll storeA w (rev (l)) )
) \/
(
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (l1: (@list A)) (l2: (@list A)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll storeA v l2 )
|--
  “ (l1 = (rev (l))) ”
  &&  emp
).

Definition reverse_return_wit_1_split_goal_1 := 
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (l1: (@list A)) (l2: (@list A)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll storeA v l2 )
|--
  “ (l1 = (rev (l))) ”
.

Definition reverse_return_wit_1_split_goal_spatial := 
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (l1: (@list A)) (l2: (@list A)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll storeA v l2 )
|--
  TT && emp 
.

Module Type VC_Correct.

Include poly_sll_Strategy_Correct.

Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_entail_wit_3 : reverse_entail_wit_3.
Axiom proof_of_reverse_entail_wit_4 : reverse_entail_wit_4.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.

End VC_Correct.
