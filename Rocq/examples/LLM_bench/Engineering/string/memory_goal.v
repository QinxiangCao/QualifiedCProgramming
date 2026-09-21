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
forall (n_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((sublist (0) (0) (bytes)) = (@nil Z)) ”
  &&  emp
).

Definition memcpy_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  ((sublist (0) (0) (bytes)) = (@nil Z))
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
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 1)) (PreH8 : (all_ascii memory )) (PreH9 : (0 <= source)) (PreH10 : (0 <= destination)) (PreH11 : ((source + n_pre ) <= (Zlength (memory)))) (PreH12 : ((destination + n_pre ) <= (Zlength (memory)))) (PreH13 : (src_pre = (base + source ))) (PreH14 : (dest_pre = (base + destination ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full base (Zlength (memory)) memory )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memmove_safety_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n_pre)) ,
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

Definition memmove_safety_wit_3 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 1)) (PreH6 : (all_ascii memory )) (PreH7 : (0 <= destination)) (PreH8 : (destination < source)) (PreH9 : ((source + n0 ) <= (Zlength (memory)))) (PreH10 : ((destination + n0 ) <= (Zlength (memory)))) (PreH11 : (src0 = (base + source ))) (PreH12 : (dest0 = (base + destination ))) (PreH13 : (value = (Znth ((source + i )) (memory) (0)))) ,
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (replace_Znth ((i - (-destination) )) ((signed_last_nbits (value) (8))) ((memmove_content (memory) (source) (destination) (i)))) )
  **  ((( &( "dest" ) )) # Ptr  |-> dest0)
  **  ((( &( "src" ) )) # Ptr  |-> src0)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "value" ) )) # Int  |-> value)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memmove_safety_wit_4 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 0)) (PreH6 : (all_ascii bytes )) (PreH7 : ((Zlength (bytes)) = n0)) (PreH8 : (value = (Znth (i) (bytes) (0)))) ,
  (CharArray.full dest0 (i + 1 ) (app ((sublist (0) (i) (bytes))) ((cons ((signed_last_nbits (value) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg dest0 (i + 1 ) n0 )
  **  ((( &( "dest" ) )) # Ptr  |-> dest0)
  **  ((( &( "src" ) )) # Ptr  |-> src0)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.full src0 n0 bytes )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memmove_safety_wit_5 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i <= n0)) (PreH5 : (mode = 1)) (PreH6 : (all_ascii memory )) (PreH7 : (0 <= source)) (PreH8 : (source <= destination)) (PreH9 : ((source + n0 ) <= (Zlength (memory)))) (PreH10 : ((destination + n0 ) <= (Zlength (memory)))) (PreH11 : (src0 = (base + source ))) (PreH12 : (dest0 = (base + destination ))) ,
  ((( &( "dest" ) )) # Ptr  |-> dest0)
  **  ((( &( "src" ) )) # Ptr  |-> src0)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memmove_safety_wit_6 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i <= n0)) (PreH5 : (mode = 0)) (PreH6 : (all_ascii bytes )) (PreH7 : ((Zlength (bytes)) = n0)) ,
  ((( &( "dest" ) )) # Ptr  |-> dest0)
  **  ((( &( "src" ) )) # Ptr  |-> src0)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg dest0 0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memmove_safety_wit_7 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= source)) (PreH9 : (source <= destination)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  ((( &( "dest" ) )) # Ptr  |-> dest0)
  **  ((( &( "src" ) )) # Ptr  |-> src0)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition memmove_safety_wit_8 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) ,
  ((( &( "dest" ) )) # Ptr  |-> dest0)
  **  ((( &( "src" ) )) # Ptr  |-> src0)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg dest0 0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition memmove_entail_wit_1_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 1)) (PreH8 : (all_ascii memory )) (PreH9 : (0 <= source)) (PreH10 : (0 <= destination)) (PreH11 : ((source + n_pre ) <= (Zlength (memory)))) (PreH12 : ((destination + n_pre ) <= (Zlength (memory)))) (PreH13 : (src_pre = (base + source ))) (PreH14 : (dest_pre = (base + destination ))) ,
  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full base (Zlength (memory)) memory )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (mode = 1) ” 
  &&  “ (all_ascii memory ) ” 
  &&  “ (0 <= destination) ” 
  &&  “ (destination < source) ” 
  &&  “ ((source + n0 ) <= (Zlength (memory))) ” 
  &&  “ ((destination + n0 ) <= (Zlength (memory))) ” 
  &&  “ (src0 = (base + source )) ” 
  &&  “ (dest0 = (base + destination )) ”
  &&  ((( &( "dest" ) )) # Ptr  |-> dest0)
  **  ((( &( "src" ) )) # Ptr  |-> src0)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (0)) )
) \/
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (PreH1 : (0 <= (Zlength (memory)))) (PreH2 : (dest_pre < src_pre)) (PreH3 : (dest_pre = dest0)) (PreH4 : (src_pre = src0)) (PreH5 : (n_pre = n0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (mode = 1)) (PreH9 : (all_ascii memory )) (PreH10 : (0 <= source)) (PreH11 : (0 <= destination)) (PreH12 : ((source + n_pre ) <= (Zlength (memory)))) (PreH13 : ((destination + n_pre ) <= (Zlength (memory)))) (PreH14 : (src_pre = (base + source ))) (PreH15 : (dest_pre = (base + destination ))) ,
  (CharArray.full base (Zlength (memory)) memory )
|--
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (0)) )
).

Definition memmove_entail_wit_1_1_split_goal_spatial := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (PreH1 : (0 <= (Zlength (memory)))) (PreH2 : (dest_pre < src_pre)) (PreH3 : (dest_pre = dest0)) (PreH4 : (src_pre = src0)) (PreH5 : (n_pre = n0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (mode = 1)) (PreH9 : (all_ascii memory )) (PreH10 : (0 <= source)) (PreH11 : (0 <= destination)) (PreH12 : ((source + n_pre ) <= (Zlength (memory)))) (PreH13 : ((destination + n_pre ) <= (Zlength (memory)))) (PreH14 : (src_pre = (base + source ))) (PreH15 : (dest_pre = (base + destination ))) ,
  (CharArray.full base (Zlength (memory)) memory )
|--
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (0)) )
.

Definition memmove_entail_wit_1_2 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n_pre)) ,
  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (mode = 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n0) ”
  &&  ((( &( "dest" ) )) # Ptr  |-> dest0)
  **  ((( &( "src" ) )) # Ptr  |-> src0)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  (CharArray.full dest0 0 (sublist (0) (0) (bytes)) )
  **  (CharArray.undef_seg dest0 0 n0 )
  **  (CharArray.full src0 n0 bytes )
) \/
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n_pre)) ,
  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ ((sublist (0) (0) (bytes)) = (@nil Z)) ”
  &&  (CharArray.undef_full dest0 n0 )
  **  (CharArray.full src0 n0 bytes )
).

Definition memmove_entail_wit_1_2_split_goal_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n_pre)) ,
  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ ((sublist (0) (0) (bytes)) = (@nil Z)) ”
.

Definition memmove_entail_wit_1_2_split_goal_spatial := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (PreH1 : (dest_pre < src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n_pre)) ,
  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  (CharArray.undef_full dest0 n0 )
  **  (CharArray.full src0 n0 bytes )
.

Definition memmove_entail_wit_2_1 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i < n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= destination)) (PreH9 : (destination < source)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (i)) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n0) ” 
  &&  “ (mode = 1) ” 
  &&  “ (all_ascii memory ) ” 
  &&  “ (0 <= destination) ” 
  &&  “ (destination < source) ” 
  &&  “ ((source + n0 ) <= (Zlength (memory))) ” 
  &&  “ ((destination + n0 ) <= (Zlength (memory))) ” 
  &&  “ (src0 = (base + source )) ” 
  &&  “ (dest0 = (base + destination )) ” 
  &&  “ ((Znth (i - (-source) ) (memmove_content (memory) (source) (destination) (i)) 0) = (Znth ((source + i )) (memory) (0))) ”
  &&  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (memmove_content (memory) (source) (destination) (i)) )
) \/
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i < n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= destination)) (PreH9 : (destination < source)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (i)) )
|--
  “ ((Znth (i - (-source) ) (memmove_content (memory) (source) (destination) (i)) 0) = (Znth ((source + i )) (memory) (0))) ”
  &&  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (memmove_content (memory) (source) (destination) (i)) )
).

Definition memmove_entail_wit_2_1_split_goal_1 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i < n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= destination)) (PreH9 : (destination < source)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (i)) )
|--
  “ ((Znth (i - (-source) ) (memmove_content (memory) (source) (destination) (i)) 0) = (Znth ((source + i )) (memory) (0))) ”
.

Definition memmove_entail_wit_2_1_split_goal_spatial := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i < n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= destination)) (PreH9 : (destination < source)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (i)) )
|--
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (memmove_content (memory) (source) (destination) (i)) )
.

Definition memmove_entail_wit_2_2 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) ,
  (CharArray.full src0 n0 bytes )
  **  (CharArray.full dest0 i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest0 i n0 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n0) ” 
  &&  “ (mode = 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n0) ” 
  &&  “ ((Znth i bytes 0) = (Znth (i) (bytes) (0))) ”
  &&  (CharArray.full dest0 i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest0 i n0 )
  **  (CharArray.full src0 n0 bytes )
.

Definition memmove_entail_wit_3_1 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 1)) (PreH6 : (all_ascii memory )) (PreH7 : (0 <= destination)) (PreH8 : (destination < source)) (PreH9 : ((source + n0 ) <= (Zlength (memory)))) (PreH10 : ((destination + n0 ) <= (Zlength (memory)))) (PreH11 : (src0 = (base + source ))) (PreH12 : (dest0 = (base + destination ))) (PreH13 : (value = (Znth ((source + i )) (memory) (0)))) ,
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (replace_Znth ((i - (-destination) )) ((signed_last_nbits (value) (8))) ((memmove_content (memory) (source) (destination) (i)))) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n0) ” 
  &&  “ (mode = 1) ” 
  &&  “ (all_ascii memory ) ” 
  &&  “ (0 <= destination) ” 
  &&  “ (destination < source) ” 
  &&  “ ((source + n0 ) <= (Zlength (memory))) ” 
  &&  “ ((destination + n0 ) <= (Zlength (memory))) ” 
  &&  “ (src0 = (base + source )) ” 
  &&  “ (dest0 = (base + destination )) ”
  &&  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) ((i + 1 ))) )
) \/
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 1)) (PreH6 : (all_ascii memory )) (PreH7 : (0 <= destination)) (PreH8 : (destination < source)) (PreH9 : ((source + n0 ) <= (Zlength (memory)))) (PreH10 : ((destination + n0 ) <= (Zlength (memory)))) (PreH11 : (src0 = (base + source ))) (PreH12 : (dest0 = (base + destination ))) (PreH13 : (value = (Znth ((source + i )) (memory) (0)))) ,
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (replace_Znth ((i - (-destination) )) ((signed_last_nbits (value) (8))) ((memmove_content (memory) (source) (destination) (i)))) )
|--
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) ((i + 1 ))) )
).

Definition memmove_entail_wit_3_1_split_goal_spatial := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 1)) (PreH6 : (all_ascii memory )) (PreH7 : (0 <= destination)) (PreH8 : (destination < source)) (PreH9 : ((source + n0 ) <= (Zlength (memory)))) (PreH10 : ((destination + n0 ) <= (Zlength (memory)))) (PreH11 : (src0 = (base + source ))) (PreH12 : (dest0 = (base + destination ))) (PreH13 : (value = (Znth ((source + i )) (memory) (0)))) ,
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (replace_Znth ((i - (-destination) )) ((signed_last_nbits (value) (8))) ((memmove_content (memory) (source) (destination) (i)))) )
|--
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) ((i + 1 ))) )
.

Definition memmove_entail_wit_3_2 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 0)) (PreH6 : (all_ascii bytes )) (PreH7 : ((Zlength (bytes)) = n0)) (PreH8 : (value = (Znth (i) (bytes) (0)))) ,
  (CharArray.full dest0 (i + 1 ) (app ((sublist (0) (i) (bytes))) ((cons ((signed_last_nbits (value) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg dest0 (i + 1 ) n0 )
  **  (CharArray.full src0 n0 bytes )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n0) ” 
  &&  “ (mode = 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n0) ”
  &&  (CharArray.full dest0 (i + 1 ) (sublist (0) ((i + 1 )) (bytes)) )
  **  (CharArray.undef_seg dest0 (i + 1 ) n0 )
  **  (CharArray.full src0 n0 bytes )
) \/
(
forall (n0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 0)) (PreH6 : (all_ascii bytes )) (PreH7 : ((Zlength (bytes)) = n0)) (PreH8 : (value = (Znth (i) (bytes) (0)))) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (i) (bytes))) ((cons ((signed_last_nbits (value) (8))) ((@nil Z))))) = (sublist (0) ((i + 1 )) (bytes))) ”
  &&  emp
).

Definition memmove_entail_wit_3_2_split_goal_1 := 
forall (n0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 0)) (PreH6 : (all_ascii bytes )) (PreH7 : ((Zlength (bytes)) = n0)) (PreH8 : (value = (Znth (i) (bytes) (0)))) ,
  ((app ((sublist (0) (i) (bytes))) ((cons ((signed_last_nbits (value) (8))) ((@nil Z))))) = (sublist (0) ((i + 1 )) (bytes)))
.

Definition memmove_entail_wit_4_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (PreH1 : (dest_pre >= src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 1)) (PreH8 : (all_ascii memory )) (PreH9 : (0 <= source)) (PreH10 : (0 <= destination)) (PreH11 : ((source + n_pre ) <= (Zlength (memory)))) (PreH12 : ((destination + n_pre ) <= (Zlength (memory)))) (PreH13 : (src_pre = (base + source ))) (PreH14 : (dest_pre = (base + destination ))) ,
  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full base (Zlength (memory)) memory )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n0) ” 
  &&  “ (mode = 1) ” 
  &&  “ (all_ascii memory ) ” 
  &&  “ (0 <= source) ” 
  &&  “ (source <= destination) ” 
  &&  “ ((source + n0 ) <= (Zlength (memory))) ” 
  &&  “ ((destination + n0 ) <= (Zlength (memory))) ” 
  &&  “ (src0 = (base + source )) ” 
  &&  “ (dest0 = (base + destination )) ”
  &&  ((( &( "dest" ) )) # Ptr  |-> dest0)
  **  ((( &( "src" ) )) # Ptr  |-> src0)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + n_pre )) ((destination + n_pre )) ((n0 - n_pre ))) )
) \/
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (PreH1 : (0 <= (Zlength (memory)))) (PreH2 : (dest_pre >= src_pre)) (PreH3 : (dest_pre = dest0)) (PreH4 : (src_pre = src0)) (PreH5 : (n_pre = n0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (mode = 1)) (PreH9 : (all_ascii memory )) (PreH10 : (0 <= source)) (PreH11 : (0 <= destination)) (PreH12 : ((source + n_pre ) <= (Zlength (memory)))) (PreH13 : ((destination + n_pre ) <= (Zlength (memory)))) (PreH14 : (src_pre = (base + source ))) (PreH15 : (dest_pre = (base + destination ))) ,
  (CharArray.full base (Zlength (memory)) memory )
|--
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + n_pre )) ((destination + n_pre )) ((n0 - n_pre ))) )
).

Definition memmove_entail_wit_4_1_split_goal_spatial := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (PreH1 : (0 <= (Zlength (memory)))) (PreH2 : (dest_pre >= src_pre)) (PreH3 : (dest_pre = dest0)) (PreH4 : (src_pre = src0)) (PreH5 : (n_pre = n0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (mode = 1)) (PreH9 : (all_ascii memory )) (PreH10 : (0 <= source)) (PreH11 : (0 <= destination)) (PreH12 : ((source + n_pre ) <= (Zlength (memory)))) (PreH13 : ((destination + n_pre ) <= (Zlength (memory)))) (PreH14 : (src_pre = (base + source ))) (PreH15 : (dest_pre = (base + destination ))) ,
  (CharArray.full base (Zlength (memory)) memory )
|--
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + n_pre )) ((destination + n_pre )) ((n0 - n_pre ))) )
.

Definition memmove_entail_wit_4_2 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (PreH1 : (dest_pre >= src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n_pre)) ,
  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n0) ” 
  &&  “ (mode = 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n0) ”
  &&  ((( &( "dest" ) )) # Ptr  |-> dest0)
  **  ((( &( "src" ) )) # Ptr  |-> src0)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  (CharArray.undef_seg dest0 0 n_pre )
  **  (CharArray.full (dest0 + (n_pre * sizeof(CHAR))) (n0 - n_pre ) (sublist (n_pre) (n0) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
) \/
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (PreH1 : (dest_pre >= src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n_pre)) ,
  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ ((sublist (n_pre) (n_pre) (bytes)) = (@nil Z)) ”
  &&  (CharArray.undef_full dest0 n_pre )
  **  (CharArray.full src0 n0 bytes )
).

Definition memmove_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (PreH1 : (dest_pre >= src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n_pre)) ,
  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ ((sublist (n_pre) (n_pre) (bytes)) = (@nil Z)) ”
.

Definition memmove_entail_wit_4_2_split_goal_spatial := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (PreH1 : (dest_pre >= src_pre)) (PreH2 : (dest_pre = dest0)) (PreH3 : (src_pre = src0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n_pre)) ,
  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  (CharArray.undef_full dest0 n_pre )
  **  (CharArray.full src0 n0 bytes )
.

Definition memmove_entail_wit_5_1 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= source)) (PreH9 : (source <= destination)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n0) ” 
  &&  “ (mode = 1) ” 
  &&  “ (all_ascii memory ) ” 
  &&  “ (0 <= source) ” 
  &&  “ (source <= destination) ” 
  &&  “ ((source + n0 ) <= (Zlength (memory))) ” 
  &&  “ ((destination + n0 ) <= (Zlength (memory))) ” 
  &&  “ (src0 = (base + source )) ” 
  &&  “ (dest0 = (base + destination )) ” 
  &&  “ ((Znth ((i - 1 ) - (-source) ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) 0) = (Znth ((source + (i - 1 ) )) (memory) (0))) ”
  &&  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (memmove_content (memory) ((source + ((i - 1 ) + 1 ) )) ((destination + ((i - 1 ) + 1 ) )) ((n0 - ((i - 1 ) + 1 ) ))) )
) \/
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= source)) (PreH9 : (source <= destination)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
|--
  “ ((Znth ((i - 1 ) - (-source) ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) 0) = (Znth ((source + (i - 1 ) )) (memory) (0))) ”
  &&  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (memmove_content (memory) ((source + ((i - 1 ) + 1 ) )) ((destination + ((i - 1 ) + 1 ) )) ((n0 - ((i - 1 ) + 1 ) ))) )
).

Definition memmove_entail_wit_5_1_split_goal_1 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= source)) (PreH9 : (source <= destination)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
|--
  “ ((Znth ((i - 1 ) - (-source) ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) 0) = (Znth ((source + (i - 1 ) )) (memory) (0))) ”
.

Definition memmove_entail_wit_5_1_split_goal_spatial := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= source)) (PreH9 : (source <= destination)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
|--
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (memmove_content (memory) ((source + ((i - 1 ) + 1 ) )) ((destination + ((i - 1 ) + 1 ) )) ((n0 - ((i - 1 ) + 1 ) ))) )
.

Definition memmove_entail_wit_5_2 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= (n0 - i ))) (PreH2 : (i > 0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n0)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n0)) ,
  (CharArray.full src0 n0 bytes )
  **  (CharArray.undef_seg dest0 0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n0) ” 
  &&  “ (mode = 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n0) ” 
  &&  “ ((Znth (i - 1 ) bytes 0) = (Znth ((i - 1 )) (bytes) (0))) ”
  &&  (CharArray.undef_seg dest0 0 ((i - 1 ) + 1 ) )
  **  (CharArray.full (dest0 + (((i - 1 ) + 1 ) * sizeof(CHAR))) (n0 - ((i - 1 ) + 1 ) ) (sublist (((i - 1 ) + 1 )) (n0) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
) \/
(
forall (n0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= (n0 - i ))) (PreH2 : (i > 0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n0)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n0)) ,
  (CharArray.undef_seg dest0 0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
|--
  (CharArray.undef_full dest0 ((i - 1 ) + 1 ) )
  **  (CharArray.full (dest0 + (((i - 1 ) + 1 ) * sizeof(CHAR))) (n0 - ((i - 1 ) + 1 ) ) (sublist (((i - 1 ) + 1 )) (n0) (bytes)) )
).

Definition memmove_entail_wit_5_2_split_goal_spatial := 
forall (n0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= (n0 - i ))) (PreH2 : (i > 0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n0)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n0)) ,
  (CharArray.undef_seg dest0 0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
|--
  (CharArray.undef_full dest0 ((i - 1 ) + 1 ) )
  **  (CharArray.full (dest0 + (((i - 1 ) + 1 ) * sizeof(CHAR))) (n0 - ((i - 1 ) + 1 ) ) (sublist (((i - 1 ) + 1 )) (n0) (bytes)) )
.

Definition memmove_entail_wit_6_1 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 1)) (PreH6 : (all_ascii memory )) (PreH7 : (0 <= source)) (PreH8 : (source <= destination)) (PreH9 : ((source + n0 ) <= (Zlength (memory)))) (PreH10 : ((destination + n0 ) <= (Zlength (memory)))) (PreH11 : (src0 = (base + source ))) (PreH12 : (dest0 = (base + destination ))) (PreH13 : (value = (Znth ((source + i )) (memory) (0)))) ,
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (replace_Znth ((i - (-destination) )) ((signed_last_nbits (value) (8))) ((memmove_content (memory) ((source + (i + 1 ) )) ((destination + (i + 1 ) )) ((n0 - (i + 1 ) ))))) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (mode = 1) ” 
  &&  “ (all_ascii memory ) ” 
  &&  “ (0 <= source) ” 
  &&  “ (source <= destination) ” 
  &&  “ ((source + n0 ) <= (Zlength (memory))) ” 
  &&  “ ((destination + n0 ) <= (Zlength (memory))) ” 
  &&  “ (src0 = (base + source )) ” 
  &&  “ (dest0 = (base + destination )) ”
  &&  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
) \/
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 1)) (PreH6 : (all_ascii memory )) (PreH7 : (0 <= source)) (PreH8 : (source <= destination)) (PreH9 : ((source + n0 ) <= (Zlength (memory)))) (PreH10 : ((destination + n0 ) <= (Zlength (memory)))) (PreH11 : (src0 = (base + source ))) (PreH12 : (dest0 = (base + destination ))) (PreH13 : (value = (Znth ((source + i )) (memory) (0)))) ,
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (replace_Znth ((i - (-destination) )) ((signed_last_nbits (value) (8))) ((memmove_content (memory) ((source + (i + 1 ) )) ((destination + (i + 1 ) )) ((n0 - (i + 1 ) ))))) )
|--
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
).

Definition memmove_entail_wit_6_1_split_goal_spatial := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 1)) (PreH6 : (all_ascii memory )) (PreH7 : (0 <= source)) (PreH8 : (source <= destination)) (PreH9 : ((source + n0 ) <= (Zlength (memory)))) (PreH10 : ((destination + n0 ) <= (Zlength (memory)))) (PreH11 : (src0 = (base + source ))) (PreH12 : (dest0 = (base + destination ))) (PreH13 : (value = (Znth ((source + i )) (memory) (0)))) ,
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (replace_Znth ((i - (-destination) )) ((signed_last_nbits (value) (8))) ((memmove_content (memory) ((source + (i + 1 ) )) ((destination + (i + 1 ) )) ((n0 - (i + 1 ) ))))) )
|--
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
.

Definition memmove_entail_wit_6_2 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= (n0 - (i + 1 ) ))) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i < n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) (PreH9 : (value = (Znth (i) (bytes) (0)))) ,
  (CharArray.undef_seg dest0 0 i )
  **  (((dest0 + (i * sizeof(CHAR)))) # Char  |-> (signed_last_nbits (value) (8)))
  **  (CharArray.full (dest0 + ((i + 1 ) * sizeof(CHAR))) (n0 - (i + 1 ) ) (sublist ((i + 1 )) (n0) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (mode = 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n0) ”
  &&  (CharArray.undef_seg dest0 0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
) \/
(
forall (n0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= (n0 - (i + 1 ) ))) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i < n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) (PreH9 : (value = (Znth (i) (bytes) (0)))) ,
  (CharArray.undef_seg dest0 0 i )
  **  (((dest0 + (i * sizeof(CHAR)))) # Char  |-> (signed_last_nbits (value) (8)))
  **  (CharArray.full (dest0 + ((i + 1 ) * sizeof(CHAR))) (n0 - (i + 1 ) ) (sublist ((i + 1 )) (n0) (bytes)) )
|--
  (CharArray.undef_full dest0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
).

Definition memmove_entail_wit_6_2_split_goal_spatial := 
forall (n0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= (n0 - (i + 1 ) ))) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i < n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) (PreH9 : (value = (Znth (i) (bytes) (0)))) ,
  (CharArray.undef_seg dest0 0 i )
  **  (((dest0 + (i * sizeof(CHAR)))) # Char  |-> (signed_last_nbits (value) (8)))
  **  (CharArray.full (dest0 + ((i + 1 ) * sizeof(CHAR))) (n0 - (i + 1 ) ) (sublist ((i + 1 )) (n0) (bytes)) )
|--
  (CharArray.undef_full dest0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
.

Definition memmove_return_wit_1 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i >= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= destination)) (PreH9 : (destination < source)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (i)) )
|--
  “ (dest0 = dest0) ” 
  &&  “ (mode = 1) ”
  &&  (CharArray.full base (Zlength (memory)) (memmove_content (memory) (source) (destination) (n0)) )
) \/
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i >= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= destination)) (PreH9 : (destination < source)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (i)) )
|--
  (CharArray.full base (Zlength (memory)) (memmove_content (memory) (source) (destination) (n0)) )
).

Definition memmove_return_wit_1_split_goal_spatial := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i >= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= destination)) (PreH9 : (destination < source)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (i)) )
|--
  (CharArray.full base (Zlength (memory)) (memmove_content (memory) (source) (destination) (n0)) )
.

Definition memmove_return_wit_2 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) ,
  (CharArray.full dest0 i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest0 i n0 )
  **  (CharArray.full src0 n0 bytes )
|--
  “ (dest0 = dest0) ” 
  &&  “ (mode = 0) ”
  &&  (CharArray.full dest0 n0 bytes )
  **  (CharArray.full src0 n0 bytes )
) \/
(
forall (n0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) ,
  (CharArray.full dest0 i (sublist (0) (i) (bytes)) )
|--
  (CharArray.full dest0 n0 bytes )
).

Definition memmove_return_wit_2_split_goal_spatial := 
forall (n0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) ,
  (CharArray.full dest0 i (sublist (0) (i) (bytes)) )
|--
  (CharArray.full dest0 n0 bytes )
.

Definition memmove_return_wit_3 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i <= 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= source)) (PreH9 : (source <= destination)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
|--
  “ (dest0 = dest0) ” 
  &&  “ (mode = 1) ”
  &&  (CharArray.full base (Zlength (memory)) (memmove_content (memory) (source) (destination) (n0)) )
) \/
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i <= 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= source)) (PreH9 : (source <= destination)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
|--
  (CharArray.full base (Zlength (memory)) (memmove_content (memory) (source) (destination) (n0)) )
).

Definition memmove_return_wit_3_split_goal_spatial := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i <= 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= source)) (PreH9 : (source <= destination)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
|--
  (CharArray.full base (Zlength (memory)) (memmove_content (memory) (source) (destination) (n0)) )
.

Definition memmove_return_wit_4 := 
(
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i <= 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) ,
  (CharArray.undef_seg dest0 0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
|--
  “ (dest0 = dest0) ” 
  &&  “ (mode = 0) ”
  &&  (CharArray.full dest0 n0 bytes )
  **  (CharArray.full src0 n0 bytes )
) \/
(
forall (n0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= (n0 - i ))) (PreH2 : (i <= 0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n0)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n0)) ,
  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
|--
  (CharArray.full dest0 n0 bytes )
).

Definition memmove_return_wit_4_split_goal_spatial := 
forall (n0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (0 <= (n0 - i ))) (PreH2 : (i <= 0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n0)) (PreH7 : (mode = 0)) (PreH8 : (all_ascii bytes )) (PreH9 : ((Zlength (bytes)) = n0)) ,
  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
|--
  (CharArray.full dest0 n0 bytes )
.

Definition memmove_partial_solve_wit_1 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i < n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= destination)) (PreH9 : (destination < source)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (i)) )
|--
  “ (i < n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (mode = 1) ” 
  &&  “ (all_ascii memory ) ” 
  &&  “ (0 <= destination) ” 
  &&  “ (destination < source) ” 
  &&  “ ((source + n0 ) <= (Zlength (memory))) ” 
  &&  “ ((destination + n0 ) <= (Zlength (memory))) ” 
  &&  “ (src0 = (base + source )) ” 
  &&  “ (dest0 = (base + destination )) ”
  &&  (((src0 + (i * sizeof(CHAR)))) # Char  |-> (Znth (i - (-source) ) (memmove_content (memory) (source) (destination) (i)) 0))
  **  (CharArray.missing_i src0 i (-source) ((Zlength (memory)) - source ) (memmove_content (memory) (source) (destination) (i)) )
.

Definition memmove_partial_solve_wit_2 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) ,
  (CharArray.full dest0 i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest0 i n0 )
  **  (CharArray.full src0 n0 bytes )
|--
  “ (i < n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (mode = 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n0) ”
  &&  (((src0 + (i * sizeof(CHAR)))) # Char  |-> (Znth i bytes 0))
  **  (CharArray.missing_i src0 i 0 n0 bytes )
  **  (CharArray.full dest0 i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest0 i n0 )
.

Definition memmove_partial_solve_wit_3 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 1)) (PreH6 : (all_ascii memory )) (PreH7 : (0 <= destination)) (PreH8 : (destination < source)) (PreH9 : ((source + n0 ) <= (Zlength (memory)))) (PreH10 : ((destination + n0 ) <= (Zlength (memory)))) (PreH11 : (src0 = (base + source ))) (PreH12 : (dest0 = (base + destination ))) (PreH13 : (value = (Znth ((source + i )) (memory) (0)))) ,
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (memmove_content (memory) (source) (destination) (i)) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n0) ” 
  &&  “ (mode = 1) ” 
  &&  “ (all_ascii memory ) ” 
  &&  “ (0 <= destination) ” 
  &&  “ (destination < source) ” 
  &&  “ ((source + n0 ) <= (Zlength (memory))) ” 
  &&  “ ((destination + n0 ) <= (Zlength (memory))) ” 
  &&  “ (src0 = (base + source )) ” 
  &&  “ (dest0 = (base + destination )) ” 
  &&  “ (value = (Znth ((source + i )) (memory) (0))) ”
  &&  (((dest0 + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dest0 i (-destination) ((Zlength (memory)) - destination ) (memmove_content (memory) (source) (destination) (i)) )
.

Definition memmove_partial_solve_wit_4 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 0)) (PreH6 : (all_ascii bytes )) (PreH7 : ((Zlength (bytes)) = n0)) (PreH8 : (value = (Znth (i) (bytes) (0)))) ,
  (CharArray.full dest0 i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest0 i n0 )
  **  (CharArray.full src0 n0 bytes )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n0) ” 
  &&  “ (mode = 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n0) ” 
  &&  “ (value = (Znth (i) (bytes) (0))) ”
  &&  (((dest0 + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i dest0 i i n0 )
  **  (CharArray.full dest0 i (sublist (0) (i) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
.

Definition memmove_partial_solve_wit_5 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 1)) (PreH7 : (all_ascii memory )) (PreH8 : (0 <= source)) (PreH9 : (source <= destination)) (PreH10 : ((source + n0 ) <= (Zlength (memory)))) (PreH11 : ((destination + n0 ) <= (Zlength (memory)))) (PreH12 : (src0 = (base + source ))) (PreH13 : (dest0 = (base + destination ))) ,
  (CharArray.seg src0 (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
|--
  “ (i > 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (mode = 1) ” 
  &&  “ (all_ascii memory ) ” 
  &&  “ (0 <= source) ” 
  &&  “ (source <= destination) ” 
  &&  “ ((source + n0 ) <= (Zlength (memory))) ” 
  &&  “ ((destination + n0 ) <= (Zlength (memory))) ” 
  &&  “ (src0 = (base + source )) ” 
  &&  “ (dest0 = (base + destination )) ”
  &&  (((src0 + ((i - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth ((i - 1 ) - (-source) ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) 0))
  **  (CharArray.missing_i src0 (i - 1 ) (-source) ((Zlength (memory)) - source ) (memmove_content (memory) ((source + i )) ((destination + i )) ((n0 - i ))) )
.

Definition memmove_partial_solve_wit_6 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 < INT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n0)) (PreH6 : (mode = 0)) (PreH7 : (all_ascii bytes )) (PreH8 : ((Zlength (bytes)) = n0)) ,
  (CharArray.undef_seg dest0 0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
|--
  “ (0 <= (n0 - i )) ” 
  &&  “ (i > 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (mode = 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n0) ”
  &&  (((src0 + ((i - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (i - 1 ) bytes 0))
  **  (CharArray.missing_i src0 (i - 1 ) 0 n0 bytes )
  **  (CharArray.undef_seg dest0 0 i )
  **  (CharArray.full (dest0 + (i * sizeof(CHAR))) (n0 - i ) (sublist (i) (n0) (bytes)) )
.

Definition memmove_partial_solve_wit_7 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (destination: Z) (source: Z) (base: Z) (memory: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 1)) (PreH6 : (all_ascii memory )) (PreH7 : (0 <= source)) (PreH8 : (source <= destination)) (PreH9 : ((source + n0 ) <= (Zlength (memory)))) (PreH10 : ((destination + n0 ) <= (Zlength (memory)))) (PreH11 : (src0 = (base + source ))) (PreH12 : (dest0 = (base + destination ))) (PreH13 : (value = (Znth ((source + i )) (memory) (0)))) ,
  (CharArray.seg dest0 (-destination) ((Zlength (memory)) - destination ) (memmove_content (memory) ((source + (i + 1 ) )) ((destination + (i + 1 ) )) ((n0 - (i + 1 ) ))) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n0) ” 
  &&  “ (mode = 1) ” 
  &&  “ (all_ascii memory ) ” 
  &&  “ (0 <= source) ” 
  &&  “ (source <= destination) ” 
  &&  “ ((source + n0 ) <= (Zlength (memory))) ” 
  &&  “ ((destination + n0 ) <= (Zlength (memory))) ” 
  &&  “ (src0 = (base + source )) ” 
  &&  “ (dest0 = (base + destination )) ” 
  &&  “ (value = (Znth ((source + i )) (memory) (0))) ”
  &&  (((dest0 + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dest0 i (-destination) ((Zlength (memory)) - destination ) (memmove_content (memory) ((source + (i + 1 ) )) ((destination + (i + 1 ) )) ((n0 - (i + 1 ) ))) )
.

Definition memmove_partial_solve_wit_8 := 
forall (n0: Z) (src0: Z) (dest0: Z) (mode: Z) (bytes: (@list Z)) (i: Z) (value: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 < INT_MAX)) (PreH3 : (0 <= i)) (PreH4 : (i < n0)) (PreH5 : (mode = 0)) (PreH6 : (all_ascii bytes )) (PreH7 : ((Zlength (bytes)) = n0)) (PreH8 : (value = (Znth (i) (bytes) (0)))) ,
  (CharArray.undef_seg dest0 0 (i + 1 ) )
  **  (CharArray.full (dest0 + ((i + 1 ) * sizeof(CHAR))) (n0 - (i + 1 ) ) (sublist ((i + 1 )) (n0) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
|--
  “ (0 <= (n0 - (i + 1 ) )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n0) ” 
  &&  “ (mode = 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n0) ” 
  &&  “ (value = (Znth (i) (bytes) (0))) ”
  &&  (((dest0 + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i dest0 i 0 (i + 1 ) )
  **  (CharArray.full (dest0 + ((i + 1 ) * sizeof(CHAR))) (n0 - (i + 1 ) ) (sublist ((i + 1 )) (n0) (bytes)) )
  **  (CharArray.full src0 n0 bytes )
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
forall (n_pre: Z) (c_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) ,
  TT && emp 
|--
  “ ((repeat_Z (c_pre) (0)) = (@nil Z)) ”
  &&  emp
).

Definition memset_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (c_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) ,
  ((repeat_Z (c_pre) (0)) = (@nil Z))
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
Axiom proof_of_memmove_safety_wit_5 : memmove_safety_wit_5.
Axiom proof_of_memmove_safety_wit_6 : memmove_safety_wit_6.
Axiom proof_of_memmove_safety_wit_7 : memmove_safety_wit_7.
Axiom proof_of_memmove_safety_wit_8 : memmove_safety_wit_8.
Axiom proof_of_memmove_entail_wit_1_1 : memmove_entail_wit_1_1.
Axiom proof_of_memmove_entail_wit_1_2 : memmove_entail_wit_1_2.
Axiom proof_of_memmove_entail_wit_2_1 : memmove_entail_wit_2_1.
Axiom proof_of_memmove_entail_wit_2_2 : memmove_entail_wit_2_2.
Axiom proof_of_memmove_entail_wit_3_1 : memmove_entail_wit_3_1.
Axiom proof_of_memmove_entail_wit_3_2 : memmove_entail_wit_3_2.
Axiom proof_of_memmove_entail_wit_4_1 : memmove_entail_wit_4_1.
Axiom proof_of_memmove_entail_wit_4_2 : memmove_entail_wit_4_2.
Axiom proof_of_memmove_entail_wit_5_1 : memmove_entail_wit_5_1.
Axiom proof_of_memmove_entail_wit_5_2 : memmove_entail_wit_5_2.
Axiom proof_of_memmove_entail_wit_6_1 : memmove_entail_wit_6_1.
Axiom proof_of_memmove_entail_wit_6_2 : memmove_entail_wit_6_2.
Axiom proof_of_memmove_return_wit_1 : memmove_return_wit_1.
Axiom proof_of_memmove_return_wit_2 : memmove_return_wit_2.
Axiom proof_of_memmove_return_wit_3 : memmove_return_wit_3.
Axiom proof_of_memmove_return_wit_4 : memmove_return_wit_4.
Axiom proof_of_memmove_partial_solve_wit_1 : memmove_partial_solve_wit_1.
Axiom proof_of_memmove_partial_solve_wit_2 : memmove_partial_solve_wit_2.
Axiom proof_of_memmove_partial_solve_wit_3 : memmove_partial_solve_wit_3.
Axiom proof_of_memmove_partial_solve_wit_4 : memmove_partial_solve_wit_4.
Axiom proof_of_memmove_partial_solve_wit_5 : memmove_partial_solve_wit_5.
Axiom proof_of_memmove_partial_solve_wit_6 : memmove_partial_solve_wit_6.
Axiom proof_of_memmove_partial_solve_wit_7 : memmove_partial_solve_wit_7.
Axiom proof_of_memmove_partial_solve_wit_8 : memmove_partial_solve_wit_8.
Axiom proof_of_memset_safety_wit_1 : memset_safety_wit_1.
Axiom proof_of_memset_safety_wit_2 : memset_safety_wit_2.
Axiom proof_of_memset_entail_wit_1 : memset_entail_wit_1.
Axiom proof_of_memset_entail_wit_2 : memset_entail_wit_2.
Axiom proof_of_memset_return_wit_1 : memset_return_wit_1.
Axiom proof_of_memset_partial_solve_wit_1 : memset_partial_solve_wit_1.

End VC_Correct.
