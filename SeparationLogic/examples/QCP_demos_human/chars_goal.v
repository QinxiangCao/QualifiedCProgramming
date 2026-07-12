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
Local Open Scope sac.

(*----- Function chars_initialize -----*)

Definition chars_initialize_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Char  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.undef_full a_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition chars_initialize_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.full a_pre (i + 1 ) (app ((repeat_Z (m_pre) (i))) ((cons (m_pre) ((@nil Z))))) )
  **  (CharArray.undef_seg a_pre (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Char  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition chars_initialize_entail_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full a_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (CharArray.full a_pre 0 (repeat_Z (m_pre) (0)) )
  **  (CharArray.undef_seg a_pre 0 n_pre )
) \/
(
forall (m_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((repeat_Z (m_pre) (0)) = (@nil Z)) ”
  &&  emp
).

Definition chars_initialize_entail_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((repeat_Z (m_pre) (0)) = (@nil Z))
.

Definition chars_initialize_entail_wit_2 := 
(
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.full a_pre (i + 1 ) (app ((repeat_Z (m_pre) (i))) ((cons (m_pre) ((@nil Z))))) )
  **  (CharArray.undef_seg a_pre (i + 1 ) n_pre )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (CharArray.full a_pre (i + 1 ) (repeat_Z (m_pre) ((i + 1 ))) )
  **  (CharArray.undef_seg a_pre (i + 1 ) n_pre )
) \/
(
forall (m_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (m_pre) (i))) ((cons (m_pre) ((@nil Z))))) = (repeat_Z (m_pre) ((i + 1 )))) ”
  &&  emp
).

Definition chars_initialize_entail_wit_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((app ((repeat_Z (m_pre) (i))) ((cons (m_pre) ((@nil Z))))) = (repeat_Z (m_pre) ((i + 1 ))))
.

Definition chars_initialize_return_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.full a_pre i (repeat_Z (m_pre) (i)) )
  **  (CharArray.undef_seg a_pre i n_pre )
|--
  (CharArray.full a_pre n_pre (repeat_Z (m_pre) (n_pre)) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.full a_pre i (repeat_Z (m_pre) (i)) )
|--
  (CharArray.full a_pre n_pre (repeat_Z (m_pre) (n_pre)) )
).

Definition chars_initialize_return_wit_1_split_goal_spatial := 
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.full a_pre i (repeat_Z (m_pre) (i)) )
|--
  (CharArray.full a_pre n_pre (repeat_Z (m_pre) (n_pre)) )
.

Definition chars_initialize_partial_solve_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.full a_pre i (repeat_Z (m_pre) (i)) )
  **  (CharArray.undef_seg a_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg a_pre (i + 1 ) n_pre )
  **  (CharArray.full a_pre i (repeat_Z (m_pre) (i)) )
.

Module Type VC_Correct.


Axiom proof_of_chars_initialize_safety_wit_1 : chars_initialize_safety_wit_1.
Axiom proof_of_chars_initialize_safety_wit_2 : chars_initialize_safety_wit_2.
Axiom proof_of_chars_initialize_entail_wit_1 : chars_initialize_entail_wit_1.
Axiom proof_of_chars_initialize_entail_wit_2 : chars_initialize_entail_wit_2.
Axiom proof_of_chars_initialize_return_wit_1 : chars_initialize_return_wit_1.
Axiom proof_of_chars_initialize_partial_solve_wit_1 : chars_initialize_partial_solve_wit_1.

End VC_Correct.
