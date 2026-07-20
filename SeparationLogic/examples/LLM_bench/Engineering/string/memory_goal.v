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

(*----- Function memcpy -----*)

Definition memcpy_safety_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memcpy_safety_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memcpy_entail_wit_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (CharArray.full dest_pre 0 (sublist (0) (0) (bytes)) )
  **  (CharArray.undef_seg dest_pre 0 n_pre )
  **  (CharArray.full src_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  “ ((sublist (0) (0) (bytes)) = (@nil Z)) ”
  &&  (CharArray.undef_full dest_pre n_pre )
).

Definition memcpy_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  “ ((sublist (0) (0) (bytes)) = (@nil Z)) ”
.

Definition memcpy_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  (CharArray.undef_full dest_pre n_pre )
.

Definition memcpy_entail_wit_2 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (CharArray.full dest_pre (i + 1 ) (sublist (0) ((i + 1 )) (bytes)) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (bytes))) ”
  &&  emp
).

Definition memcpy_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  ((app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (bytes)))
.

Definition memcpy_return_wit_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (dest_pre = dest_pre) ”
  &&  (CharArray.full dest_pre n_pre bytes )
  **  (CharArray.full src_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
|--
  (CharArray.full dest_pre n_pre bytes )
).

Definition memcpy_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
|--
  (CharArray.full dest_pre n_pre bytes )
.

Definition memcpy_partial_solve_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((src_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i bytes 0))
  **  (CharArray.missing_i src_pre i 0 n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
.

Definition memcpy_partial_solve_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((dest_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i dest_pre i i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
.

(*----- Function memmove -----*)

Definition memmove_safety_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memmove_safety_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memmove_safety_wit_3 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR))) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memmove_safety_wit_4 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR))) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition memmove_entail_wit_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (CharArray.full dest_pre 0 (sublist (0) (0) (bytes)) )
  **  (CharArray.undef_seg dest_pre 0 n_pre )
  **  (CharArray.full src_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  “ ((sublist (0) (0) (bytes)) = (@nil Z)) ”
  &&  (CharArray.undef_full dest_pre n_pre )
).

Definition memmove_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  “ ((sublist (0) (0) (bytes)) = (@nil Z)) ”
.

Definition memmove_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  (CharArray.undef_full dest_pre n_pre )
.

Definition memmove_entail_wit_2 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (CharArray.full dest_pre (i + 1 ) (sublist (0) ((i + 1 )) (bytes)) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (bytes))) ”
  &&  emp
).

Definition memmove_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  ((app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (bytes)))
.

Definition memmove_entail_wit_3 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (dest_pre >= src_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ”
  &&  (CharArray.undef_seg dest_pre 0 n_pre )
  **  (CharArray.full (dest_pre + (n_pre * sizeof(CHAR))) (n_pre - n_pre ) (sublist (n_pre) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (dest_pre >= src_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  “ ((sublist (n_pre) (n_pre) (bytes)) = (@nil Z)) ”
  &&  (CharArray.undef_full dest_pre n_pre )
).

Definition memmove_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (dest_pre >= src_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  “ ((sublist (n_pre) (n_pre) (bytes)) = (@nil Z)) ”
.

Definition memmove_entail_wit_3_split_goal_spatial := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (PreH1 : (dest_pre >= src_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (CharArray.undef_full dest_pre n_pre )
|--
  (CharArray.undef_full dest_pre n_pre )
.

Definition memmove_entail_wit_4 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= (n_pre - i ))) (PreH2 : (i > 0)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) ,
  (CharArray.full (dest_pre + ((i - 1 ) * sizeof(CHAR))) ((n_pre - i ) + 1 ) (cons ((Znth (i - 1 ) bytes 0)) ((sublist (i) (n_pre) (bytes)))) )
  **  (CharArray.undef_seg dest_pre 0 (i - 1 ) )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= n_pre) ”
  &&  (CharArray.undef_seg dest_pre 0 (i - 1 ) )
  **  (CharArray.full (dest_pre + ((i - 1 ) * sizeof(CHAR))) (n_pre - (i - 1 ) ) (sublist ((i - 1 )) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= ((n_pre - i ) + 1 ))) (PreH2 : (0 <= (n_pre - i ))) (PreH3 : (i > 0)) (PreH4 : (all_ascii bytes )) (PreH5 : ((Zlength (bytes)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) ,
  (CharArray.full (dest_pre + ((i - 1 ) * sizeof(CHAR))) ((n_pre - i ) + 1 ) (cons ((Znth (i - 1 ) bytes 0)) ((sublist (i) (n_pre) (bytes)))) )
  **  (CharArray.undef_seg dest_pre 0 (i - 1 ) )
|--
  (CharArray.undef_full dest_pre (i - 1 ) )
  **  (CharArray.full (dest_pre + ((i - 1 ) * sizeof(CHAR))) (n_pre - (i - 1 ) ) (sublist ((i - 1 )) (n_pre) (bytes)) )
).

Definition memmove_entail_wit_4_split_goal_spatial := 
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= ((n_pre - i ) + 1 ))) (PreH2 : (0 <= (n_pre - i ))) (PreH3 : (i > 0)) (PreH4 : (all_ascii bytes )) (PreH5 : ((Zlength (bytes)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) ,
  (CharArray.full (dest_pre + ((i - 1 ) * sizeof(CHAR))) ((n_pre - i ) + 1 ) (cons ((Znth (i - 1 ) bytes 0)) ((sublist (i) (n_pre) (bytes)))) )
  **  (CharArray.undef_seg dest_pre 0 (i - 1 ) )
|--
  (CharArray.undef_full dest_pre (i - 1 ) )
  **  (CharArray.full (dest_pre + ((i - 1 ) * sizeof(CHAR))) (n_pre - (i - 1 ) ) (sublist ((i - 1 )) (n_pre) (bytes)) )
.

Definition memmove_return_wit_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (dest_pre = dest_pre) ”
  &&  (CharArray.full dest_pre n_pre bytes )
  **  (CharArray.full src_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
|--
  (CharArray.full dest_pre n_pre bytes )
).

Definition memmove_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
|--
  (CharArray.full dest_pre n_pre bytes )
.

Definition memmove_return_wit_2 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i <= 0)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR))) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (dest_pre = dest_pre) ”
  &&  (CharArray.full dest_pre n_pre bytes )
  **  (CharArray.full src_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= (n_pre - i ))) (PreH2 : (i <= 0)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) ,
  (CharArray.full (dest_pre + (i * sizeof(CHAR))) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
|--
  (CharArray.full dest_pre n_pre bytes )
).

Definition memmove_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= (n_pre - i ))) (PreH2 : (i <= 0)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) ,
  (CharArray.full (dest_pre + (i * sizeof(CHAR))) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
|--
  (CharArray.full dest_pre n_pre bytes )
.

Definition memmove_partial_solve_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((src_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i bytes 0))
  **  (CharArray.missing_i src_pre i 0 n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
.

Definition memmove_partial_solve_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((dest_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i dest_pre i i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
.

Definition memmove_partial_solve_wit_3 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR))) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (0 <= (n_pre - i )) ” 
  &&  “ (i > 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((src_pre + ((i - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (i - 1 ) bytes 0))
  **  (CharArray.missing_i src_pre (i - 1 ) 0 n_pre bytes )
  **  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR))) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
.

Definition memmove_partial_solve_wit_4 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= (n_pre - i ))) (PreH2 : (i > 0)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) ,
  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR))) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
|--
  “ (0 <= (n_pre - i )) ” 
  &&  “ (i > 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((dest_pre + ((i - 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i dest_pre (i - 1 ) 0 i )
  **  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR))) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
.

(*----- Function memset -----*)

Definition memset_safety_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full s_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memset_safety_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full s_pre (i + 1 ) (app ((repeat_Z (c_pre) (i))) ((cons (c_pre) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memset_entail_wit_1 := 
(
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) ,
  (CharArray.undef_full s_pre n_pre )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (CharArray.full s_pre 0 (repeat_Z (c_pre) (0)) )
  **  (CharArray.undef_seg s_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) ,
  (CharArray.undef_full s_pre n_pre )
|--
  “ ((repeat_Z (c_pre) (0)) = (@nil Z)) ”
  &&  (CharArray.undef_full s_pre n_pre )
).

Definition memset_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) ,
  (CharArray.undef_full s_pre n_pre )
|--
  “ ((repeat_Z (c_pre) (0)) = (@nil Z)) ”
.

Definition memset_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) ,
  (CharArray.undef_full s_pre n_pre )
|--
  (CharArray.undef_full s_pre n_pre )
.

Definition memset_entail_wit_2 := 
(
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full s_pre (i + 1 ) (app ((repeat_Z (c_pre) (i))) ((cons (c_pre) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (i + 1 ) n_pre )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (CharArray.full s_pre (i + 1 ) (repeat_Z (c_pre) ((i + 1 ))) )
  **  (CharArray.undef_seg s_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (c_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (c_pre) (i))) ((cons (c_pre) ((@nil Z))))) = (repeat_Z (c_pre) ((i + 1 )))) ”
  &&  emp
).

Definition memset_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (c_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  ((app ((repeat_Z (c_pre) (i))) ((cons (c_pre) ((@nil Z))))) = (repeat_Z (c_pre) ((i + 1 ))))
.

Definition memset_return_wit_1 := 
(
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full s_pre i (repeat_Z (c_pre) (i)) )
  **  (CharArray.undef_seg s_pre i n_pre )
|--
  “ (s_pre = s_pre) ”
  &&  (CharArray.full s_pre n_pre (repeat_Z (c_pre) (n_pre)) )
) \/
(
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full s_pre i (repeat_Z (c_pre) (i)) )
|--
  (CharArray.full s_pre n_pre (repeat_Z (c_pre) (n_pre)) )
).

Definition memset_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full s_pre i (repeat_Z (c_pre) (i)) )
|--
  (CharArray.full s_pre n_pre (repeat_Z (c_pre) (n_pre)) )
.

Definition memset_partial_solve_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) ,
  (CharArray.full s_pre i (repeat_Z (c_pre) (i)) )
  **  (CharArray.undef_seg s_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i s_pre i i n_pre )
  **  (CharArray.full s_pre i (repeat_Z (c_pre) (i)) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_memcpy_safety_wit_1 : memcpy_safety_wit_1.
Axiom proof_of_memcpy_safety_wit_2 : memcpy_safety_wit_2.
Axiom proof_of_memcpy_entail_wit_1 : memcpy_entail_wit_1.
Axiom proof_of_memcpy_entail_wit_2 : memcpy_entail_wit_2.
Axiom proof_of_memcpy_return_wit_1 : memcpy_return_wit_1.
Axiom proof_of_memcpy_partial_solve_wit_1 : memcpy_partial_solve_wit_1.
Axiom proof_of_memcpy_partial_solve_wit_2 : memcpy_partial_solve_wit_2.
Axiom proof_of_memmove_safety_wit_1 : memmove_safety_wit_1.
Axiom proof_of_memmove_safety_wit_2 : memmove_safety_wit_2.
Axiom proof_of_memmove_safety_wit_3 : memmove_safety_wit_3.
Axiom proof_of_memmove_safety_wit_4 : memmove_safety_wit_4.
Axiom proof_of_memmove_entail_wit_1 : memmove_entail_wit_1.
Axiom proof_of_memmove_entail_wit_2 : memmove_entail_wit_2.
Axiom proof_of_memmove_entail_wit_3 : memmove_entail_wit_3.
Axiom proof_of_memmove_entail_wit_4 : memmove_entail_wit_4.
Axiom proof_of_memmove_return_wit_1 : memmove_return_wit_1.
Axiom proof_of_memmove_return_wit_2 : memmove_return_wit_2.
Axiom proof_of_memmove_partial_solve_wit_1 : memmove_partial_solve_wit_1.
Axiom proof_of_memmove_partial_solve_wit_2 : memmove_partial_solve_wit_2.
Axiom proof_of_memmove_partial_solve_wit_3 : memmove_partial_solve_wit_3.
Axiom proof_of_memmove_partial_solve_wit_4 : memmove_partial_solve_wit_4.
Axiom proof_of_memset_safety_wit_1 : memset_safety_wit_1.
Axiom proof_of_memset_safety_wit_2 : memset_safety_wit_2.
Axiom proof_of_memset_entail_wit_1 : memset_entail_wit_1.
Axiom proof_of_memset_entail_wit_2 : memset_entail_wit_2.
Axiom proof_of_memset_return_wit_1 : memset_return_wit_1.
Axiom proof_of_memset_partial_solve_wit_1 : memset_partial_solve_wit_1.

End VC_Correct.
