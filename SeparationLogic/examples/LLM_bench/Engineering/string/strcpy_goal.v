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
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function strcpy -----*)

Definition strcpy_safety_wit_1 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (valid_string src_str )) (PreH2 : ((string_length (src_str)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.undef_full dest_pre ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcpy_safety_wit_2 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (valid_string src_str )) (PreH2 : ((string_length (src_str)) < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i <= (string_length (src_str)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcpy_safety_wit_3 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH3 : (valid_string src_str )) (PreH4 : ((string_length (src_str)) < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) ((string_length (src_str)) + 1 ) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strcpy_safety_wit_4 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (src_str)) 0) = 0)) (PreH2 : (valid_string src_str )) (PreH3 : ((string_length (src_str)) < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= (string_length (src_str)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcpy_entail_wit_1 := 
(
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (valid_string src_str )) (PreH2 : ((string_length (src_str)) < INT_MAX)) ,
  (CharArray.undef_full dest_pre ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre 0 (sublist (0) (0) (src_str)) )
  **  (CharArray.undef_seg dest_pre 0 ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
) \/
(
forall (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (valid_string src_str )) (PreH3 : ((string_length (src_str)) < INT_MAX)) ,
  (CharArray.undef_full dest_pre ((string_length (src_str)) + 1 ) )
|--
  “ (0 <= (string_length (src_str))) ” 
  &&  “ ((sublist (0) (0) (src_str)) = (@nil Z)) ”
  &&  (CharArray.undef_full dest_pre ((string_length (src_str)) + 1 ) )
).

Definition strcpy_entail_wit_1_split_goal_1 := 
forall (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (valid_string src_str )) (PreH3 : ((string_length (src_str)) < INT_MAX)) ,
  (CharArray.undef_full dest_pre ((string_length (src_str)) + 1 ) )
|--
  “ (0 <= (string_length (src_str))) ”
.

Definition strcpy_entail_wit_1_split_goal_2 := 
forall (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (valid_string src_str )) (PreH3 : ((string_length (src_str)) < INT_MAX)) ,
  (CharArray.undef_full dest_pre ((string_length (src_str)) + 1 ) )
|--
  “ ((sublist (0) (0) (src_str)) = (@nil Z)) ”
.

Definition strcpy_entail_wit_1_split_goal_spatial := 
forall (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (valid_string src_str )) (PreH3 : ((string_length (src_str)) < INT_MAX)) ,
  (CharArray.undef_full dest_pre ((string_length (src_str)) + 1 ) )
|--
  (CharArray.undef_full dest_pre ((string_length (src_str)) + 1 ) )
.

Definition strcpy_entail_wit_2 := 
(
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH3 : (valid_string src_str )) (PreH4 : ((string_length (src_str)) < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) ((string_length (src_str)) + 1 ) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
|--
  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (i + 1 ) (sublist (0) ((i + 1 )) (src_str)) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
) \/
(
forall (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH3 : (valid_string src_str )) (PreH4 : ((string_length (src_str)) < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (src_str)))) ,
  TT && emp 
|--
  “ ((i + 1 ) <= (string_length (src_str))) ” 
  &&  “ ((app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (src_str))) ”
  &&  emp
).

Definition strcpy_entail_wit_2_split_goal_1 := 
forall (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH3 : (valid_string src_str )) (PreH4 : ((string_length (src_str)) < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (src_str)))) ,
  ((i + 1 ) <= (string_length (src_str)))
.

Definition strcpy_entail_wit_2_split_goal_2 := 
forall (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH3 : (valid_string src_str )) (PreH4 : ((string_length (src_str)) < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (src_str)))) ,
  ((app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (src_str)))
.

Definition strcpy_return_wit_1 := 
(
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) = 0)) (PreH3 : (valid_string src_str )) (PreH4 : ((string_length (src_str)) < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) ((string_length (src_str)) + 1 ) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
|--
  “ (dest_pre = dest_pre) ”
  &&  (store_string dest_pre src_str )
  **  (store_string src_pre src_str )
) \/
(
forall (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : (0 <= ((string_length (src_str)) + 1 ))) (PreH3 : ((Znth i (c_string (src_str)) 0) = 0)) (PreH4 : (valid_string src_str )) (PreH5 : ((string_length (src_str)) < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) ((string_length (src_str)) + 1 ) )
|--
  (CharArray.full dest_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
).

Definition strcpy_return_wit_1_split_goal_spatial := 
forall (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : (0 <= ((string_length (src_str)) + 1 ))) (PreH3 : ((Znth i (c_string (src_str)) 0) = 0)) (PreH4 : (valid_string src_str )) (PreH5 : ((string_length (src_str)) < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) ((string_length (src_str)) + 1 ) )
|--
  (CharArray.full dest_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
.

Definition strcpy_partial_solve_wit_1 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH2 : (valid_string src_str )) (PreH3 : ((string_length (src_str)) < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) <> 0) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (((dest_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.undef_missing_i dest_pre i i ((string_length (src_str)) + 1 ) )
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
.

Definition strcpy_partial_solve_wit_2 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (src_str)) 0) = 0)) (PreH2 : (valid_string src_str )) (PreH3 : ((string_length (src_str)) < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) = 0) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (((dest_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.undef_missing_i dest_pre i i ((string_length (src_str)) + 1 ) )
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
.

(*----- Function strncpy -----*)

Definition strncpy_safety_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (valid_string src_str )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full dest_pre n_pre )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncpy_safety_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (valid_string src_str )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (i <= (string_length (src_str)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncpy_safety_wit_3 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string src_str )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strncpy_safety_wit_4 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (valid_string src_str )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (strncpy_content src_str i out )) (PreH8 : ((i < n_pre) -> ((string_length (src_str)) <= i))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full dest_pre i out )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncpy_safety_wit_5 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string src_str )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (strncpy_content src_str i out )) (PreH9 : ((i < n_pre) -> ((string_length (src_str)) <= i))) ,
  (CharArray.full dest_pre (i + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strncpy_entail_wit_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (valid_string src_str )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
  **  (store_string src_pre src_str )
|--
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre 0 (sublist (0) (0) (src_str)) )
  **  (CharArray.undef_seg dest_pre 0 n_pre )
  **  (store_string src_pre src_str )
) \/
(
forall (n_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (valid_string src_str )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  “ (0 <= (string_length (src_str))) ” 
  &&  “ ((sublist (0) (0) (src_str)) = (@nil Z)) ”
  &&  (CharArray.undef_full dest_pre n_pre )
).

Definition strncpy_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (valid_string src_str )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  “ (0 <= (string_length (src_str))) ”
.

Definition strncpy_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (valid_string src_str )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  “ ((sublist (0) (0) (src_str)) = (@nil Z)) ”
.

Definition strncpy_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (valid_string src_str )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  (CharArray.undef_full dest_pre n_pre )
.

Definition strncpy_entail_wit_2 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string src_str )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
|--
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (i + 1 ) (sublist (0) ((i + 1 )) (src_str)) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (store_string src_pre src_str )
) \/
(
forall (n_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string src_str )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (i <= (string_length (src_str)))) ,
  TT && emp 
|--
  “ ((i + 1 ) <= (string_length (src_str))) ” 
  &&  “ ((app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (src_str))) ”
  &&  emp
).

Definition strncpy_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string src_str )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (i <= (string_length (src_str)))) ,
  ((i + 1 ) <= (string_length (src_str)))
.

Definition strncpy_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string src_str )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (i <= (string_length (src_str)))) ,
  ((app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (src_str)))
.

Definition strncpy_entail_wit_3_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (valid_string src_str )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  EX (out: (@list Z)) ,
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  (CharArray.full dest_pre i out )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
) \/
(
forall (n_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string src_str )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i <= (string_length (src_str)))) ,
  TT && emp 
|--
  “ (strncpy_content src_str i (sublist (0) (i) (src_str)) ) ”
  &&  (CharArray.undef_seg dest_pre i n_pre )
).

Definition strncpy_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string src_str )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i <= (string_length (src_str)))) ,
  (strncpy_content src_str i (sublist (0) (i) (src_str)) )
.

Definition strncpy_entail_wit_3_1_split_goal_spatial := 
forall (n_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string src_str )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i <= (string_length (src_str)))) ,
  TT && emp 
|--
  (CharArray.undef_seg dest_pre i n_pre )
.

Definition strncpy_entail_wit_3_2 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (src_str)) 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (valid_string src_str )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  EX (out: (@list Z)) ,
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  (CharArray.full dest_pre i out )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
) \/
(
forall (n_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string src_str )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (i <= (string_length (src_str)))) ,
  TT && emp 
|--
  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ” 
  &&  “ (strncpy_content src_str i (sublist (0) (i) (src_str)) ) ”
  &&  emp
).

Definition strncpy_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string src_str )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (i <= (string_length (src_str)))) ,
  ((i < n_pre) -> ((string_length (src_str)) <= i))
.

Definition strncpy_entail_wit_3_2_split_goal_2 := 
forall (n_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : ((Znth i (c_string (src_str)) 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string src_str )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (i <= (string_length (src_str)))) ,
  (strncpy_content src_str i (sublist (0) (i) (src_str)) )
.

Definition strncpy_entail_wit_4 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string src_str )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (strncpy_content src_str i out_2 )) (PreH9 : ((i < n_pre) -> ((string_length (src_str)) <= i))) ,
  (CharArray.full dest_pre (i + 1 ) (app (out_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
|--
  EX (out: (@list Z)) ,
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (strncpy_content src_str (i + 1 ) out ) ” 
  &&  “ (((i + 1 ) < n_pre) -> ((string_length (src_str)) <= (i + 1 ))) ”
  &&  (CharArray.full dest_pre (i + 1 ) out )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (store_string src_pre src_str )
) \/
(
forall (n_pre: Z) (src_str: (@list Z)) (out_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string src_str )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (strncpy_content src_str i out_2 )) (PreH9 : ((i < n_pre) -> ((string_length (src_str)) <= i))) ,
  TT && emp 
|--
  “ (strncpy_content src_str (i + 1 ) (app (out_2) ((cons (0) ((@nil Z))))) ) ”
  &&  emp
).

Definition strncpy_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (src_str: (@list Z)) (out_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string src_str )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (strncpy_content src_str i out_2 )) (PreH9 : ((i < n_pre) -> ((string_length (src_str)) <= i))) ,
  (strncpy_content src_str (i + 1 ) (app (out_2) ((cons (0) ((@nil Z))))) )
.

Definition strncpy_return_wit_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (valid_string src_str )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (strncpy_content src_str i out_2 )) (PreH8 : ((i < n_pre) -> ((string_length (src_str)) <= i))) ,
  (CharArray.full dest_pre i out_2 )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  EX (out: (@list Z)) ,
  “ (strncpy_content src_str n_pre out ) ” 
  &&  “ (dest_pre = dest_pre) ”
  &&  (CharArray.full dest_pre n_pre out )
  **  (store_string src_pre src_str )
) \/
(
forall (n_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (src_str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string src_str )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (strncpy_content src_str i out_2 )) (PreH9 : ((i < n_pre) -> ((string_length (src_str)) <= i))) ,
  (CharArray.full dest_pre i out_2 )
|--
  EX (out: (@list Z)) ,
  “ (strncpy_content src_str n_pre out ) ”
  &&  (CharArray.full dest_pre n_pre out )
).

Definition strncpy_partial_solve_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (src_str)) 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (valid_string src_str )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i <= (string_length (src_str)))) ,
  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (((dest_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.undef_missing_i dest_pre i i n_pre )
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
.

Definition strncpy_partial_solve_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (valid_string src_str )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (strncpy_content src_str i out )) (PreH8 : ((i < n_pre) -> ((string_length (src_str)) <= i))) ,
  (CharArray.full dest_pre i out )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  (((dest_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.undef_missing_i dest_pre i i n_pre )
  **  (CharArray.full dest_pre i out )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_strcpy_safety_wit_1 : strcpy_safety_wit_1.
Axiom proof_of_strcpy_safety_wit_2 : strcpy_safety_wit_2.
Axiom proof_of_strcpy_safety_wit_3 : strcpy_safety_wit_3.
Axiom proof_of_strcpy_safety_wit_4 : strcpy_safety_wit_4.
Axiom proof_of_strcpy_entail_wit_1 : strcpy_entail_wit_1.
Axiom proof_of_strcpy_entail_wit_2 : strcpy_entail_wit_2.
Axiom proof_of_strcpy_return_wit_1 : strcpy_return_wit_1.
Axiom proof_of_strcpy_partial_solve_wit_1 : strcpy_partial_solve_wit_1.
Axiom proof_of_strcpy_partial_solve_wit_2 : strcpy_partial_solve_wit_2.
Axiom proof_of_strncpy_safety_wit_1 : strncpy_safety_wit_1.
Axiom proof_of_strncpy_safety_wit_2 : strncpy_safety_wit_2.
Axiom proof_of_strncpy_safety_wit_3 : strncpy_safety_wit_3.
Axiom proof_of_strncpy_safety_wit_4 : strncpy_safety_wit_4.
Axiom proof_of_strncpy_safety_wit_5 : strncpy_safety_wit_5.
Axiom proof_of_strncpy_entail_wit_1 : strncpy_entail_wit_1.
Axiom proof_of_strncpy_entail_wit_2 : strncpy_entail_wit_2.
Axiom proof_of_strncpy_entail_wit_3_1 : strncpy_entail_wit_3_1.
Axiom proof_of_strncpy_entail_wit_3_2 : strncpy_entail_wit_3_2.
Axiom proof_of_strncpy_entail_wit_4 : strncpy_entail_wit_4.
Axiom proof_of_strncpy_return_wit_1 : strncpy_return_wit_1.
Axiom proof_of_strncpy_partial_solve_wit_1 : strncpy_partial_solve_wit_1.
Axiom proof_of_strncpy_partial_solve_wit_2 : strncpy_partial_solve_wit_2.

End VC_Correct.
