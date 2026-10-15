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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 100001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 100001 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 100001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 100001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 100001 )
|--
  “ (50 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 50) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 50)
  **  (CharArray.undef_seg out_pre 1 100001 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (chars: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars)) = i)) (PreH7 : ((Znth 0 chars 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars 0) = 51))) ,
  (CharArray.seg out_pre 0 (i + 1 ) (app (chars) ((cons (51) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (i + 1 ) 100001 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (n_pre: Z) (chars: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars)) = i)) (PreH7 : ((Znth 0 chars 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars 0) = 51))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.seg out_pre 0 i chars )
  **  (CharArray.undef_seg out_pre i 100001 )
|--
  “ (51 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 51) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (n_pre: Z) (chars: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars)) = i)) (PreH7 : ((Znth 0 chars 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars 0) = 51))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.seg out_pre 0 i chars )
  **  (CharArray.undef_seg out_pre i 100001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 50)
  **  (CharArray.undef_seg out_pre 1 100001 )
|--
  EX (chars: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (chars)) = 1) ” 
  &&  “ ((Znth 0 chars 0) = 50) ” 
  &&  “ forall (k: Z) , (((1 <= k) /\ (k < 1)) -> ((Znth k chars 0) = 51)) ”
  &&  (CharArray.seg out_pre 0 1 chars )
  **  (CharArray.undef_seg out_pre 1 100001 )
) \/
(
forall (out_pre: Z) (n_pre: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 50)
|--
  EX (chars: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (chars)) = 1) ” 
  &&  “ ((Znth 0 chars 0) = 50) ” 
  &&  “ forall (k: Z) , (((1 <= k) /\ (k < 1)) -> ((Znth k chars 0) = 51)) ”
  &&  (CharArray.seg out_pre 0 1 chars )
).

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (n_pre: Z) (chars_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i)) (PreH7 : ((Znth 0 chars_2 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars_2 0) = 51))) ,
  (CharArray.seg out_pre 0 (i + 1 ) (app (chars_2) ((cons (51) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (i + 1 ) 100001 )
|--
  EX (chars: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (chars)) = (i + 1 )) ” 
  &&  “ ((Znth 0 chars 0) = 50) ” 
  &&  “ forall (k: Z) , (((1 <= k) /\ (k < (i + 1 ))) -> ((Znth k chars 0) = 51)) ”
  &&  (CharArray.seg out_pre 0 (i + 1 ) chars )
  **  (CharArray.undef_seg out_pre (i + 1 ) 100001 )
) \/
(
forall (n_pre: Z) (chars_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i)) (PreH7 : ((Znth 0 chars_2 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars_2 0) = 51))) ,
  TT && emp 
|--
  “ ((Znth 0 (app (chars_2) ((cons (51) ((@nil Z))))) 0) = 50) ” 
  &&  “ ((Zlength ((app (chars_2) ((cons (51) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (chars_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i)) (PreH7 : ((Znth 0 chars_2 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars_2 0) = 51))) ,
  ((Znth 0 (app (chars_2) ((cons (51) ((@nil Z))))) 0) = 50)
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (chars_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i)) (PreH7 : ((Znth 0 chars_2 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars_2 0) = 51))) ,
  ((Zlength ((app (chars_2) ((cons (51) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (chars_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i_2)) (PreH7 : ((Znth 0 chars_2 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i_2)) -> ((Znth k chars_2 0) = 51))) ,
  (CharArray.seg out_pre 0 (i_2 + 1 ) (app (chars_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (i_2 + 1 ) 100001 )
|--
  EX (chars: (@list Z))  (digits: (@list Z)) ,
  “ (Spec n_pre (Some (digits)) ) ” 
  &&  “ ((Zlength (chars)) = (Zlength (digits))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (digits)))) -> ((Znth i chars 0) = ((Znth i digits 0) + 48 ))) ” 
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  (CharArray.full out_pre ((Zlength (chars)) + 1 ) (app (chars) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (chars)) + 1 ) 100001 )
) \/
(
forall (out_pre: Z) (n_pre: Z) (chars_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i_2)) (PreH7 : ((Znth 0 chars_2 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i_2)) -> ((Znth k chars_2 0) = 51))) ,
  (CharArray.seg out_pre 0 (i_2 + 1 ) (app (chars_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (i_2 + 1 ) 100001 )
|--
  EX (chars: (@list Z))  (digits: (@list Z)) ,
  “ (Spec n_pre (Some (digits)) ) ” 
  &&  “ ((Zlength (chars)) = (Zlength (digits))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (digits)))) -> ((Znth i chars 0) = ((Znth i digits 0) + 48 ))) ” 
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  (CharArray.full out_pre ((Zlength (chars)) + 1 ) (app (chars) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (chars)) + 1 ) 100001 )
).

Definition solver_return_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (CharArray.undef_full out_pre 100001 )
|--
  (“ ((-1) = (-1)) ” 
  &&  “ (Spec n_pre None ) ”
  &&  (CharArray.undef_full out_pre 100001 ))
  ||
  (EX (chars: (@list Z))  (digits: (@list Z)) ,
  “ (Spec n_pre (Some (digits)) ) ” 
  &&  “ ((Zlength (chars)) = (Zlength (digits))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (digits)))) -> ((Znth i chars 0) = ((Znth i digits 0) + 48 ))) ” 
  &&  “ ((-1) = (Zlength (digits))) ”
  &&  (CharArray.full out_pre ((Zlength (chars)) + 1 ) (app (chars) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (chars)) + 1 ) 100001 ))
.

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (CharArray.undef_full out_pre 100001 )
|--
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ”
  &&  (((out_pre + (0 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg out_pre 1 100001 )
.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (chars: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars)) = i)) (PreH7 : ((Znth 0 chars 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars 0) = 51))) ,
  (CharArray.seg out_pre 0 i chars )
  **  (CharArray.undef_seg out_pre i 100001 )
|--
  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (chars)) = i) ” 
  &&  “ ((Znth 0 chars 0) = 50) ” 
  &&  “ forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars 0) = 51)) ”
  &&  (((out_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg out_pre (i + 1 ) 100001 )
  **  (CharArray.seg out_pre 0 i chars )
.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (chars: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars)) = i)) (PreH7 : ((Znth 0 chars 0) = 50)) (PreH8 : forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars 0) = 51))) ,
  (CharArray.seg out_pre 0 i chars )
  **  (CharArray.undef_seg out_pre i 100001 )
|--
  “ (i >= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (chars)) = i) ” 
  &&  “ ((Znth 0 chars 0) = 50) ” 
  &&  “ forall (k: Z) , (((1 <= k) /\ (k < i)) -> ((Znth k chars 0) = 51)) ”
  &&  (((out_pre + (n_pre * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre n_pre i 100001 )
  **  (CharArray.seg out_pre 0 i chars )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
