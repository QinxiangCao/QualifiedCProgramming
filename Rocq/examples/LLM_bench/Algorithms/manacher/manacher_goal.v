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
Require Import SimpleC.EE.LLM_bench.Algorithms.manacher.manacher_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function longestPalindrom -----*)

Definition longestPalindrom_safety_wit_1 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_2 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_3 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_4 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  ((( &( "id" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_5 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  ((( &( "limit" ) )) # Int  |->_)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_6 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  ((( &( "maxLen" ) )) # Int  |->_)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_7 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  ((( &( "maxId" ) )) # Int  |->_)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_8 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_9 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  ((( &( "mirror" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_10 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_11 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  (IntArray.undef_full ( &( "p" ) ) 2003 )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_12 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  (IntArray.undef_full ( &( "p" ) ) 2003 )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_13 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) ,
  (((( &( "p" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_14 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) ,
  (((( &( "p" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (36 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 36) ”
.

Definition longestPalindrom_safety_wit_15 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition longestPalindrom_safety_wit_16 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition longestPalindrom_safety_wit_17 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_18 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_19 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (35 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 35) ”
.

Definition longestPalindrom_safety_wit_20 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (((2 * i ) + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 2 )) ”
.

Definition longestPalindrom_safety_wit_21 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition longestPalindrom_safety_wit_22 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_23 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_24 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) ((@nil Z)))))) ((cons ((Znth i (c_string (str)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((((2 * i ) + 1 ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_25 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition longestPalindrom_safety_wit_26 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition longestPalindrom_safety_wit_27 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_28 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_29 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (35 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 35) ”
.

Definition longestPalindrom_safety_wit_30 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (((2 * i ) + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 2 )) ”
.

Definition longestPalindrom_safety_wit_31 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition longestPalindrom_safety_wit_32 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_33 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_34 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_35 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((((2 * i ) + 1 ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_36 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((((2 * i ) + 1 ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_37 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((((2 * i ) + 1 ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_38 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((((2 * i ) + 1 ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_39 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((((2 * i ) + 1 ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_40 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (i < limit)) (PreH2 : (i < len)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i <= len)) (PreH12 : (j = 0)) (PreH13 : (r = 0)) (PreH14 : (mirror = 0)) (PreH15 : (ret = 0)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : ((Zlength (s2_full)) = (len + 1 ))) (PreH25 : ((Zlength (p_cur)) = i)) (PreH26 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (((2 * id ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * id ) - i )) ”
.

Definition longestPalindrom_safety_wit_41 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (i < limit)) (PreH2 : (i < len)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i <= len)) (PreH12 : (j = 0)) (PreH13 : (r = 0)) (PreH14 : (mirror = 0)) (PreH15 : (ret = 0)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : ((Zlength (s2_full)) = (len + 1 ))) (PreH25 : ((Zlength (p_cur)) = i)) (PreH26 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((2 * id ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * id )) ”
.

Definition longestPalindrom_safety_wit_42 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (i < limit)) (PreH2 : (i < len)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i <= len)) (PreH12 : (j = 0)) (PreH13 : (r = 0)) (PreH14 : (mirror = 0)) (PreH15 : (ret = 0)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : ((Zlength (s2_full)) = (len + 1 ))) (PreH25 : ((Zlength (p_cur)) = i)) (PreH26 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_43 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i < len)) (PreH11 : (0 <= mirror)) (PreH12 : (mirror < i)) (PreH13 : (mirror = ((2 * id ) - i ))) (PreH14 : (j = 0)) (PreH15 : (r = 0)) (PreH16 : (ret = 0)) (PreH17 : (i < limit)) (PreH18 : (limit <= len)) (PreH19 : ((Zlength (s2_full)) = (len + 1 ))) (PreH20 : ((Zlength (p_cur)) = i)) (PreH21 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((limit - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (limit - i )) ”
.

Definition longestPalindrom_safety_wit_44 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((limit - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (limit - i )) ”
.

Definition longestPalindrom_safety_wit_45 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (i >= limit)) (PreH2 : (i < len)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i <= len)) (PreH12 : (j = 0)) (PreH13 : (r = 0)) (PreH14 : (mirror = 0)) (PreH15 : (ret = 0)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : ((Zlength (s2_full)) = (len + 1 ))) (PreH25 : ((Zlength (p_cur)) = i)) (PreH26 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_46 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i < len)) (PreH11 : (j = 0)) (PreH12 : (ret = 0)) (PreH13 : (1 <= r)) (PreH14 : (0 <= id)) (PreH15 : (id < len)) (PreH16 : (0 <= limit)) (PreH17 : (limit <= len)) (PreH18 : (0 <= mirror)) (PreH19 : (mirror < len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : (0 <= (i - r ))) (PreH25 : ((i + r ) <= len)) (PreH26 : ((Zlength (s2_full)) = (len + 1 ))) (PreH27 : ((Zlength (p_written)) = (i + 1 ))) (PreH28 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH29 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i - r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - r )) ”
.

Definition longestPalindrom_safety_wit_47 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (len <= 2002)) (PreH8 : (1 <= i)) (PreH9 : (i < len)) (PreH10 : (j = 0)) (PreH11 : (ret = 0)) (PreH12 : (1 <= r)) (PreH13 : (0 <= id)) (PreH14 : (id < len)) (PreH15 : (0 <= limit)) (PreH16 : (limit <= len)) (PreH17 : (0 <= mirror)) (PreH18 : (mirror < len)) (PreH19 : (0 <= maxLen)) (PreH20 : (maxLen <= n_pre)) (PreH21 : (0 <= maxId)) (PreH22 : (maxId < len)) (PreH23 : (0 <= (i - r ))) (PreH24 : ((i + r ) <= len)) (PreH25 : ((Zlength (s2_full)) = (len + 1 ))) (PreH26 : ((Zlength (p_written)) = (i + 1 ))) (PreH27 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH28 : (ExpansionCandidate s2_full len i r )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + r )) ”
.

Definition longestPalindrom_safety_wit_48 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_written: (@list Z)) (len: Z) (i: Z) (j: Z) (ret: Z) (r: Z) (id: Z) (limit: Z) (mirror: Z) (maxLen: Z) (maxId: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (len <= 2002)) (PreH8 : (1 <= i)) (PreH9 : (i < len)) (PreH10 : (j = 0)) (PreH11 : (ret = 0)) (PreH12 : (1 <= r)) (PreH13 : (0 <= id)) (PreH14 : (id < len)) (PreH15 : (0 <= limit)) (PreH16 : (limit <= len)) (PreH17 : (0 <= mirror)) (PreH18 : (mirror < len)) (PreH19 : (0 <= maxLen)) (PreH20 : (maxLen <= n_pre)) (PreH21 : (0 <= maxId)) (PreH22 : (maxId < len)) (PreH23 : (0 < (i - r ))) (PreH24 : ((i + r ) < len)) (PreH25 : ((Zlength (s2_full)) = (len + 1 ))) (PreH26 : ((Zlength (p_written)) = (i + 1 ))) (PreH27 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH28 : (ExpansionAfterMatch s2_full len i r )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition longestPalindrom_safety_wit_49 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (j = 0)) (PreH13 : (ret = 0)) (PreH14 : (1 <= r)) (PreH15 : (0 <= id)) (PreH16 : (id < len)) (PreH17 : (0 <= limit)) (PreH18 : (limit <= len)) (PreH19 : (0 <= mirror)) (PreH20 : (mirror < len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : (0 <= (i - r ))) (PreH26 : ((i + r ) <= len)) (PreH27 : ((Zlength (s2_full)) = (len + 1 ))) (PreH28 : ((Zlength (p_written)) = (i + 1 ))) (PreH29 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH30 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + r )) ”
.

Definition longestPalindrom_safety_wit_50 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((i + r ) > limit)) (PreH2 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH3 : (0 <= ((string_length (str)) + 1 ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i < len)) (PreH13 : (j = 0)) (PreH14 : (ret = 0)) (PreH15 : (1 <= r)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= mirror)) (PreH21 : (mirror < len)) (PreH22 : (0 <= maxLen)) (PreH23 : (maxLen <= n_pre)) (PreH24 : (0 <= maxId)) (PreH25 : (maxId < len)) (PreH26 : (0 <= (i - r ))) (PreH27 : ((i + r ) <= len)) (PreH28 : ((Zlength (s2_full)) = (len + 1 ))) (PreH29 : ((Zlength (p_written)) = (i + 1 ))) (PreH30 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH31 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + r )) ”
.

Definition longestPalindrom_safety_wit_51 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((i + r ) > limit)) (PreH2 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH3 : (0 <= ((string_length (str)) + 1 ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i < len)) (PreH13 : (j = 0)) (PreH14 : (ret = 0)) (PreH15 : (1 <= r)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= mirror)) (PreH21 : (mirror < len)) (PreH22 : (0 <= maxLen)) (PreH23 : (maxLen <= n_pre)) (PreH24 : (0 <= maxId)) (PreH25 : (maxId < len)) (PreH26 : (0 <= (i - r ))) (PreH27 : ((i + r ) <= len)) (PreH28 : ((Zlength (s2_full)) = (len + 1 ))) (PreH29 : ((Zlength (p_written)) = (i + 1 ))) (PreH30 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH31 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((r - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r - 1 )) ”
.

Definition longestPalindrom_safety_wit_52 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((i + r ) > limit)) (PreH2 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH3 : (0 <= ((string_length (str)) + 1 ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i < len)) (PreH13 : (j = 0)) (PreH14 : (ret = 0)) (PreH15 : (1 <= r)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= mirror)) (PreH21 : (mirror < len)) (PreH22 : (0 <= maxLen)) (PreH23 : (maxLen <= n_pre)) (PreH24 : (0 <= maxId)) (PreH25 : (maxId < len)) (PreH26 : (0 <= (i - r ))) (PreH27 : ((i + r ) <= len)) (PreH28 : ((Zlength (s2_full)) = (len + 1 ))) (PreH29 : ((Zlength (p_written)) = (i + 1 ))) (PreH30 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH31 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_53 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((i + r ) <= limit)) (PreH2 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH3 : (0 <= ((string_length (str)) + 1 ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i < len)) (PreH13 : (j = 0)) (PreH14 : (ret = 0)) (PreH15 : (1 <= r)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= mirror)) (PreH21 : (mirror < len)) (PreH22 : (0 <= maxLen)) (PreH23 : (maxLen <= n_pre)) (PreH24 : (0 <= maxId)) (PreH25 : (maxId < len)) (PreH26 : (0 <= (i - r ))) (PreH27 : ((i + r ) <= len)) (PreH28 : ((Zlength (s2_full)) = (len + 1 ))) (PreH29 : ((Zlength (p_written)) = (i + 1 ))) (PreH30 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH31 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((r - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r - 1 )) ”
.

Definition longestPalindrom_safety_wit_54 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((i + r ) <= limit)) (PreH2 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH3 : (0 <= ((string_length (str)) + 1 ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i < len)) (PreH13 : (j = 0)) (PreH14 : (ret = 0)) (PreH15 : (1 <= r)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= mirror)) (PreH21 : (mirror < len)) (PreH22 : (0 <= maxLen)) (PreH23 : (maxLen <= n_pre)) (PreH24 : (0 <= maxId)) (PreH25 : (maxId < len)) (PreH26 : (0 <= (i - r ))) (PreH27 : ((i + r ) <= len)) (PreH28 : ((Zlength (s2_full)) = (len + 1 ))) (PreH29 : ((Zlength (p_written)) = (i + 1 ))) (PreH30 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH31 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_55 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_56 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_57 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_58 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_59 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_60 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_61 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_62 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_63 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_64 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_65 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_66 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_67 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (i >= len)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i <= len)) (PreH11 : (j = 0)) (PreH12 : (r = 0)) (PreH13 : (mirror = 0)) (PreH14 : (ret = 0)) (PreH15 : (0 <= id)) (PreH16 : (id < len)) (PreH17 : (0 <= limit)) (PreH18 : (limit <= len)) (PreH19 : (0 <= maxLen)) (PreH20 : (maxLen <= n_pre)) (PreH21 : (0 <= maxId)) (PreH22 : (maxId < len)) (PreH23 : ((Zlength (s2_full)) = (len + 1 ))) (PreH24 : ((Zlength (p_cur)) = i)) (PreH25 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_68 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (i >= len)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i <= len)) (PreH11 : (j = 0)) (PreH12 : (r = 0)) (PreH13 : (mirror = 0)) (PreH14 : (ret = 0)) (PreH15 : (0 <= id)) (PreH16 : (id < len)) (PreH17 : (0 <= limit)) (PreH18 : (limit <= len)) (PreH19 : (0 <= maxLen)) (PreH20 : (maxLen <= n_pre)) (PreH21 : (0 <= maxId)) (PreH22 : (maxId < len)) (PreH23 : ((Zlength (s2_full)) = (len + 1 ))) (PreH24 : ((Zlength (p_cur)) = i)) (PreH25 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((maxId - maxLen ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (maxId - maxLen )) ”
.

Definition longestPalindrom_safety_wit_69 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (len <= 2002)) (PreH8 : (1 <= maxLen)) (PreH9 : (0 <= maxLen)) (PreH10 : (maxLen <= n_pre)) (PreH11 : (0 <= (maxId - maxLen ))) (PreH12 : ((maxId + maxLen ) < len)) (PreH13 : ((maxId - maxLen ) <= i)) (PreH14 : (i <= ((maxId + maxLen ) + 1 ))) (PreH15 : (0 <= j)) (PreH16 : (j <= maxLen)) (PreH17 : (r = 0)) (PreH18 : (mirror = 0)) (PreH19 : (ret = 0)) (PreH20 : (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j )) (PreH21 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen ))) (PreH22 : ((Zlength (s2_full)) = (len + 1 ))) (PreH23 : ((Zlength (p_done)) = len)) (PreH24 : (ManacherLoopState str s2_full len p_done len id limit maxId maxLen )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((maxId + maxLen ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (maxId + maxLen )) ”
.

Definition longestPalindrom_safety_wit_70 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i <= (maxId + maxLen ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= maxLen)) (PreH11 : (0 <= maxLen)) (PreH12 : (maxLen <= n_pre)) (PreH13 : (0 <= (maxId - maxLen ))) (PreH14 : ((maxId + maxLen ) < len)) (PreH15 : ((maxId - maxLen ) <= i)) (PreH16 : (i <= ((maxId + maxLen ) + 1 ))) (PreH17 : (0 <= j)) (PreH18 : (j <= maxLen)) (PreH19 : (r = 0)) (PreH20 : (mirror = 0)) (PreH21 : (ret = 0)) (PreH22 : (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j )) (PreH23 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen ))) (PreH24 : ((Zlength (s2_full)) = (len + 1 ))) (PreH25 : ((Zlength (p_done)) = len)) (PreH26 : (ManacherLoopState str s2_full len p_done len id limit maxId maxLen )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ (35 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 35) ”
.

Definition longestPalindrom_safety_wit_71 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full 0) <> 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full)) = (len + 1 ))) (PreH26 : ((Zlength (p_done)) = len)) (PreH27 : (ManacherLoopState str s2_full len p_done len id limit maxId maxLen )) ,
  (CharArray.full output_pre (j + 1 ) (app (out_prefix) ((cons ((Znth (i - 0 ) s2_full 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition longestPalindrom_safety_wit_72 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full 0) <> 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full)) = (len + 1 ))) (PreH26 : ((Zlength (p_done)) = len)) (PreH27 : (ManacherLoopState str s2_full len p_done len id limit maxId maxLen )) ,
  (CharArray.full output_pre (j + 1 ) (app (out_prefix) ((cons ((Znth (i - 0 ) s2_full 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_73 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full 0) = 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full)) = (len + 1 ))) (PreH26 : ((Zlength (p_done)) = len)) (PreH27 : (ManacherLoopState str s2_full len p_done len id limit maxId maxLen )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_74 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : (i > (maxId + maxLen ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= maxLen)) (PreH10 : (0 <= maxLen)) (PreH11 : (maxLen <= n_pre)) (PreH12 : (0 <= (maxId - maxLen ))) (PreH13 : ((maxId + maxLen ) < len)) (PreH14 : ((maxId - maxLen ) <= i)) (PreH15 : (i <= ((maxId + maxLen ) + 1 ))) (PreH16 : (0 <= j)) (PreH17 : (j <= maxLen)) (PreH18 : (r = 0)) (PreH19 : (mirror = 0)) (PreH20 : (ret = 0)) (PreH21 : (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j )) (PreH22 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen ))) (PreH23 : ((Zlength (s2_full)) = (len + 1 ))) (PreH24 : ((Zlength (p_done)) = len)) (PreH25 : (ManacherLoopState str s2_full len p_done len id limit maxId maxLen )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_entail_wit_1 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) ,
  (((( &( "s2" ) ) + (0 * sizeof(CHAR)))) # Char  |-> 36)
  **  (CharArray.undef_seg ( &( "s2" ) ) 1 2003 )
  **  (((( &( "p" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  EX (p_pre: (@list Z))  (s2_pre: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * 0 ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre 0 ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * 0 ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * 0 ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (0 <= ((string_length (str)) + 1 ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) ,
  (((( &( "s2" ) ) + (0 * sizeof(CHAR)))) # Char  |-> 36)
  **  (((( &( "p" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
|--
  EX (p_pre: (@list Z))  (s2_pre: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * 0 ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre 0 ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 ((2 * 0 ) + 1 ) s2_pre )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
).

Definition longestPalindrom_entail_wit_2 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre_2: (@list Z)) (s2_pre_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre_2)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre_2)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre_2 i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre_2) ((cons (35) ((@nil Z)))))) ((cons ((Znth i (c_string (str)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((((2 * i ) + 1 ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  EX (p_pre: (@list Z))  (s2_pre: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * (i + 1 ) ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre (i + 1 ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * (i + 1 ) ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * (i + 1 ) ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (p_pre_2: (@list Z)) (s2_pre_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre_2)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre_2)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre_2 i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre_2) ((cons (35) ((@nil Z)))))) ((cons ((Znth i (c_string (str)) 0)) ((@nil Z))))) )
|--
  EX (s2_pre: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * (i + 1 ) ) + 1 )) ” 
  &&  “ ((Zlength (p_pre_2)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre (i + 1 ) ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 ((2 * (i + 1 ) ) + 1 ) s2_pre )
).

Definition longestPalindrom_entail_wit_3 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre_2: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre_2)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((((2 * i ) + 1 ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  EX (p_pre: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (((2 * i ) + 2 ) = ((2 * n_pre ) + 2 )) ” 
  &&  “ (((2 * i ) + 2 ) <= 2002) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_full)) = (((2 * i ) + 2 ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedString str s2_full ((2 * i ) + 2 ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 2 ) + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 2 ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (p_pre_2: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre_2)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
|--
  EX (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (((2 * i ) + 2 ) = ((2 * n_pre ) + 2 )) ” 
  &&  “ (((2 * i ) + 2 ) <= 2002) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_full)) = (((2 * i ) + 2 ) + 1 )) ” 
  &&  “ ((Zlength (p_pre_2)) = 1) ” 
  &&  “ (ManacherTransformedString str s2_full ((2 * i ) + 2 ) ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 2 ) + 1 ) s2_full )
).

Definition longestPalindrom_entail_wit_4 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_pre: (@list Z)) (len: Z) (i: Z) (id: Z) (limit: Z) (maxLen: Z) (maxId: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (len <= 2002)) (PreH8 : (i = 1)) (PreH9 : (id = 0)) (PreH10 : (limit = 0)) (PreH11 : (maxLen = 0)) (PreH12 : (maxId = 0)) (PreH13 : (j = 0)) (PreH14 : (r = 0)) (PreH15 : (mirror = 0)) (PreH16 : (ret = 0)) (PreH17 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH18 : ((Zlength (p_pre)) = 1)) (PreH19 : (ManacherTransformedString str s2_full_2 len )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  EX (p_cur: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_pre: (@list Z)) (len: Z) (i: Z) (id: Z) (limit: Z) (maxLen: Z) (maxId: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (i = 1)) (PreH10 : (id = 0)) (PreH11 : (limit = 0)) (PreH12 : (maxLen = 0)) (PreH13 : (maxId = 0)) (PreH14 : (j = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedString str s2_full_2 len )) ,
  TT && emp 
|--
  “ (ManacherLoopState str s2_full_2 ((2 * n_pre ) + 2 ) p_pre 1 0 0 0 0 ) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_pre: (@list Z)) (len: Z) (i: Z) (id: Z) (limit: Z) (maxLen: Z) (maxId: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (i = 1)) (PreH10 : (id = 0)) (PreH11 : (limit = 0)) (PreH12 : (maxLen = 0)) (PreH13 : (maxId = 0)) (PreH14 : (j = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedString str s2_full_2 len )) ,
  (ManacherLoopState str s2_full_2 ((2 * n_pre ) + 2 ) p_pre 1 0 0 0 0 )
.

Definition longestPalindrom_entail_wit_5 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (i < limit)) (PreH2 : (i < len)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i <= len)) (PreH12 : (j = 0)) (PreH13 : (r = 0)) (PreH14 : (mirror = 0)) (PreH15 : (ret = 0)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH25 : ((Zlength (p_cur_2)) = i)) (PreH26 : (ManacherLoopState str s2_full_2 len p_cur_2 i id limit maxId maxLen )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  EX (p_cur: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= ((2 * id ) - i )) ” 
  &&  “ (((2 * id ) - i ) < i) ” 
  &&  “ (((2 * id ) - i ) = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (p_cur_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < limit)) (PreH3 : (i < len)) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i <= len)) (PreH13 : (j = 0)) (PreH14 : (r = 0)) (PreH15 : (mirror = 0)) (PreH16 : (ret = 0)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_cur_2)) = i)) (PreH27 : (ManacherLoopState str s2_full_2 len p_cur_2 i id limit maxId maxLen )) ,
  TT && emp 
|--
  “ (((2 * id ) - i ) < i) ” 
  &&  “ (0 <= ((2 * id ) - i )) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (p_cur_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < limit)) (PreH3 : (i < len)) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i <= len)) (PreH13 : (j = 0)) (PreH14 : (r = 0)) (PreH15 : (mirror = 0)) (PreH16 : (ret = 0)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_cur_2)) = i)) (PreH27 : (ManacherLoopState str s2_full_2 len p_cur_2 i id limit maxId maxLen )) ,
  (((2 * id ) - i ) < i)
.

Definition longestPalindrom_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (str: (@list Z)) (p_cur_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < limit)) (PreH3 : (i < len)) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i <= len)) (PreH13 : (j = 0)) (PreH14 : (r = 0)) (PreH15 : (mirror = 0)) (PreH16 : (ret = 0)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_cur_2)) = i)) (PreH27 : (ManacherLoopState str s2_full_2 len p_cur_2 i id limit maxId maxLen )) ,
  (0 <= ((2 * id ) - i ))
.

Definition longestPalindrom_entail_wit_6_1 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) (app (p_cur) ((cons ((Znth (mirror - 0 ) p_cur 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= (Znth (mirror - 0 ) p_cur 0)) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - (Znth (mirror - 0 ) p_cur 0) )) ” 
  &&  “ ((i + (Znth (mirror - 0 ) p_cur 0) ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i (Znth (mirror - 0 ) p_cur 0) id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i (Znth (mirror - 0 ) p_cur 0) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  TT && emp 
|--
  “ (ExpansionCandidate s2_full_2 ((2 * n_pre ) + 2 ) i (Znth (((2 * id ) - i ) - 0 ) p_cur 0) ) ” 
  &&  “ (ExpansionLoopState str s2_full_2 ((2 * n_pre ) + 2 ) (app (p_cur) ((cons ((Znth (((2 * id ) - i ) - 0 ) p_cur 0)) ((@nil Z))))) i (Znth (((2 * id ) - i ) - 0 ) p_cur 0) id limit maxId maxLen ) ” 
  &&  “ ((Zlength ((app (p_cur) ((cons ((Znth (((2 * id ) - i ) - 0 ) p_cur 0)) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (0 <= (i - (Znth (((2 * id ) - i ) - 0 ) p_cur 0) )) ” 
  &&  “ (maxId < ((2 * n_pre ) + 2 )) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (1 <= (Znth (((2 * id ) - i ) - 0 ) p_cur 0)) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_6_1_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (ExpansionCandidate s2_full_2 ((2 * n_pre ) + 2 ) i (Znth (((2 * id ) - i ) - 0 ) p_cur 0) )
.

Definition longestPalindrom_entail_wit_6_1_split_goal_2 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (ExpansionLoopState str s2_full_2 ((2 * n_pre ) + 2 ) (app (p_cur) ((cons ((Znth (((2 * id ) - i ) - 0 ) p_cur 0)) ((@nil Z))))) i (Znth (((2 * id ) - i ) - 0 ) p_cur 0) id limit maxId maxLen )
.

Definition longestPalindrom_entail_wit_6_1_split_goal_3 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  ((Zlength ((app (p_cur) ((cons ((Znth (((2 * id ) - i ) - 0 ) p_cur 0)) ((@nil Z))))))) = (i + 1 ))
.

Definition longestPalindrom_entail_wit_6_1_split_goal_4 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (0 <= (i - (Znth (((2 * id ) - i ) - 0 ) p_cur 0) ))
.

Definition longestPalindrom_entail_wit_6_1_split_goal_5 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (maxId < ((2 * n_pre ) + 2 ))
.

Definition longestPalindrom_entail_wit_6_1_split_goal_6 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (0 <= maxId)
.

Definition longestPalindrom_entail_wit_6_1_split_goal_7 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (maxLen <= n_pre)
.

Definition longestPalindrom_entail_wit_6_1_split_goal_8 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (0 <= maxLen)
.

Definition longestPalindrom_entail_wit_6_1_split_goal_9 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (1 <= (Znth (((2 * id ) - i ) - 0 ) p_cur 0))
.

Definition longestPalindrom_entail_wit_6_2 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) (app (p_cur) ((cons ((limit - i )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= (limit - i )) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - (limit - i ) )) ” 
  &&  “ ((i + (limit - i ) ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i (limit - i ) id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i (limit - i ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  TT && emp 
|--
  “ (ExpansionCandidate s2_full_2 ((2 * n_pre ) + 2 ) i (limit - i ) ) ” 
  &&  “ (ExpansionLoopState str s2_full_2 ((2 * n_pre ) + 2 ) (app (p_cur) ((cons ((limit - i )) ((@nil Z))))) i (limit - i ) id limit maxId maxLen ) ” 
  &&  “ ((Zlength ((app (p_cur) ((cons ((limit - i )) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (0 <= (i - (limit - i ) )) ” 
  &&  “ (maxId < ((2 * n_pre ) + 2 )) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxLen) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_6_2_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (ExpansionCandidate s2_full_2 ((2 * n_pre ) + 2 ) i (limit - i ) )
.

Definition longestPalindrom_entail_wit_6_2_split_goal_2 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (ExpansionLoopState str s2_full_2 ((2 * n_pre ) + 2 ) (app (p_cur) ((cons ((limit - i )) ((@nil Z))))) i (limit - i ) id limit maxId maxLen )
.

Definition longestPalindrom_entail_wit_6_2_split_goal_3 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  ((Zlength ((app (p_cur) ((cons ((limit - i )) ((@nil Z))))))) = (i + 1 ))
.

Definition longestPalindrom_entail_wit_6_2_split_goal_4 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (0 <= (i - (limit - i ) ))
.

Definition longestPalindrom_entail_wit_6_2_split_goal_5 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (maxId < ((2 * n_pre ) + 2 ))
.

Definition longestPalindrom_entail_wit_6_2_split_goal_6 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (0 <= maxId)
.

Definition longestPalindrom_entail_wit_6_2_split_goal_7 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (maxLen <= n_pre)
.

Definition longestPalindrom_entail_wit_6_2_split_goal_8 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (0 <= maxLen)
.

Definition longestPalindrom_entail_wit_6_3 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= limit)) (PreH3 : (i < len)) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i <= len)) (PreH13 : (j = 0)) (PreH14 : (r = 0)) (PreH15 : (mirror = 0)) (PreH16 : (ret = 0)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_cur)) = i)) (PreH27 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) (app (p_cur) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i 1 id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i 1 ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= limit)) (PreH3 : (i < len)) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i <= len)) (PreH13 : (j = 0)) (PreH14 : (r = 0)) (PreH15 : (mirror = 0)) (PreH16 : (ret = 0)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_cur)) = i)) (PreH27 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  TT && emp 
|--
  “ (ExpansionCandidate s2_full_2 ((2 * n_pre ) + 2 ) i 1 ) ” 
  &&  “ (ExpansionLoopState str s2_full_2 ((2 * n_pre ) + 2 ) (app (p_cur) ((cons (1) ((@nil Z))))) i 1 id limit maxId maxLen ) ” 
  &&  “ ((Zlength ((app (p_cur) ((cons (1) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_6_3_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= limit)) (PreH3 : (i < len)) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i <= len)) (PreH13 : (j = 0)) (PreH14 : (r = 0)) (PreH15 : (mirror = 0)) (PreH16 : (ret = 0)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_cur)) = i)) (PreH27 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (ExpansionCandidate s2_full_2 ((2 * n_pre ) + 2 ) i 1 )
.

Definition longestPalindrom_entail_wit_6_3_split_goal_2 := 
forall (n_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= limit)) (PreH3 : (i < len)) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i <= len)) (PreH13 : (j = 0)) (PreH14 : (r = 0)) (PreH15 : (mirror = 0)) (PreH16 : (ret = 0)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_cur)) = i)) (PreH27 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (ExpansionLoopState str s2_full_2 ((2 * n_pre ) + 2 ) (app (p_cur) ((cons (1) ((@nil Z))))) i 1 id limit maxId maxLen )
.

Definition longestPalindrom_entail_wit_6_3_split_goal_3 := 
forall (n_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= limit)) (PreH3 : (i < len)) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= i)) (PreH12 : (i <= len)) (PreH13 : (j = 0)) (PreH14 : (r = 0)) (PreH15 : (mirror = 0)) (PreH16 : (ret = 0)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_cur)) = i)) (PreH27 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  ((Zlength ((app (p_cur) ((cons (1) ((@nil Z))))))) = (i + 1 ))
.

Definition longestPalindrom_entail_wit_7 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_written_2: (@list Z)) (len: Z) (i: Z) (j: Z) (ret: Z) (r: Z) (id: Z) (limit: Z) (mirror: Z) (maxLen: Z) (maxId: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (len <= 2002)) (PreH8 : (1 <= i)) (PreH9 : (i < len)) (PreH10 : (j = 0)) (PreH11 : (ret = 0)) (PreH12 : (1 <= r)) (PreH13 : (0 <= id)) (PreH14 : (id < len)) (PreH15 : (0 <= limit)) (PreH16 : (limit <= len)) (PreH17 : (0 <= mirror)) (PreH18 : (mirror < len)) (PreH19 : (0 <= maxLen)) (PreH20 : (maxLen <= n_pre)) (PreH21 : (0 <= maxId)) (PreH22 : (maxId < len)) (PreH23 : (0 <= (i - r ))) (PreH24 : ((i + r ) <= len)) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_written_2)) = (i + 1 ))) (PreH27 : (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen )) (PreH28 : (ExpansionCandidate s2_full_2 len i r )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_8 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((Znth ((i + r ) - 0 ) s2_full_2 0) = (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (j = 0)) (PreH13 : (ret = 0)) (PreH14 : (1 <= r)) (PreH15 : (0 <= id)) (PreH16 : (id < len)) (PreH17 : (0 <= limit)) (PreH18 : (limit <= len)) (PreH19 : (0 <= mirror)) (PreH20 : (mirror < len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : (0 <= (i - r ))) (PreH26 : ((i + r ) <= len)) (PreH27 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH28 : ((Zlength (p_written_2)) = (i + 1 ))) (PreH29 : (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen )) (PreH30 : (ExpansionCandidate s2_full_2 len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 < (i - r )) ” 
  &&  “ ((i + r ) < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionAfterMatch s2_full len i r ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (p_written_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((Znth ((i + r ) - 0 ) s2_full_2 0) = (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (j = 0)) (PreH13 : (ret = 0)) (PreH14 : (1 <= r)) (PreH15 : (0 <= id)) (PreH16 : (id < len)) (PreH17 : (0 <= limit)) (PreH18 : (limit <= len)) (PreH19 : (0 <= mirror)) (PreH20 : (mirror < len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : (0 <= (i - r ))) (PreH26 : ((i + r ) <= len)) (PreH27 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH28 : ((Zlength (p_written_2)) = (i + 1 ))) (PreH29 : (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen )) (PreH30 : (ExpansionCandidate s2_full_2 len i r )) ,
  TT && emp 
|--
  “ (ExpansionAfterMatch s2_full_2 ((2 * n_pre ) + 2 ) i r ) ” 
  &&  “ ((i + r ) < ((2 * n_pre ) + 2 )) ” 
  &&  “ (0 < (i - r )) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (p_written_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((Znth ((i + r ) - 0 ) s2_full_2 0) = (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (j = 0)) (PreH13 : (ret = 0)) (PreH14 : (1 <= r)) (PreH15 : (0 <= id)) (PreH16 : (id < len)) (PreH17 : (0 <= limit)) (PreH18 : (limit <= len)) (PreH19 : (0 <= mirror)) (PreH20 : (mirror < len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : (0 <= (i - r ))) (PreH26 : ((i + r ) <= len)) (PreH27 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH28 : ((Zlength (p_written_2)) = (i + 1 ))) (PreH29 : (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen )) (PreH30 : (ExpansionCandidate s2_full_2 len i r )) ,
  (ExpansionAfterMatch s2_full_2 ((2 * n_pre ) + 2 ) i r )
.

Definition longestPalindrom_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (str: (@list Z)) (p_written_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((Znth ((i + r ) - 0 ) s2_full_2 0) = (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (j = 0)) (PreH13 : (ret = 0)) (PreH14 : (1 <= r)) (PreH15 : (0 <= id)) (PreH16 : (id < len)) (PreH17 : (0 <= limit)) (PreH18 : (limit <= len)) (PreH19 : (0 <= mirror)) (PreH20 : (mirror < len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : (0 <= (i - r ))) (PreH26 : ((i + r ) <= len)) (PreH27 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH28 : ((Zlength (p_written_2)) = (i + 1 ))) (PreH29 : (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen )) (PreH30 : (ExpansionCandidate s2_full_2 len i r )) ,
  ((i + r ) < ((2 * n_pre ) + 2 ))
.

Definition longestPalindrom_entail_wit_8_split_goal_3 := 
forall (n_pre: Z) (str: (@list Z)) (p_written_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : ((Znth ((i + r ) - 0 ) s2_full_2 0) = (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (j = 0)) (PreH13 : (ret = 0)) (PreH14 : (1 <= r)) (PreH15 : (0 <= id)) (PreH16 : (id < len)) (PreH17 : (0 <= limit)) (PreH18 : (limit <= len)) (PreH19 : (0 <= mirror)) (PreH20 : (mirror < len)) (PreH21 : (0 <= maxLen)) (PreH22 : (maxLen <= n_pre)) (PreH23 : (0 <= maxId)) (PreH24 : (maxId < len)) (PreH25 : (0 <= (i - r ))) (PreH26 : ((i + r ) <= len)) (PreH27 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH28 : ((Zlength (p_written_2)) = (i + 1 ))) (PreH29 : (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen )) (PreH30 : (ExpansionCandidate s2_full_2 len i r )) ,
  (0 < (i - r ))
.

Definition longestPalindrom_entail_wit_9 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_written_2: (@list Z)) (len: Z) (i: Z) (j: Z) (ret: Z) (r: Z) (id: Z) (limit: Z) (mirror: Z) (maxLen: Z) (maxId: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i < len)) (PreH11 : (j = 0)) (PreH12 : (ret = 0)) (PreH13 : (1 <= r)) (PreH14 : (0 <= id)) (PreH15 : (id < len)) (PreH16 : (0 <= limit)) (PreH17 : (limit <= len)) (PreH18 : (0 <= mirror)) (PreH19 : (mirror < len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : (0 < (i - r ))) (PreH25 : ((i + r ) < len)) (PreH26 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH27 : ((Zlength (p_written_2)) = (i + 1 ))) (PreH28 : (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen )) (PreH29 : (ExpansionAfterMatch s2_full_2 len i r )) ,
  (IntArray.full ( &( "p" ) ) (i + 1 ) (replace_Znth (i) ((r + 1 )) (p_written_2)) )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= (r + 1 )) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - (r + 1 ) )) ” 
  &&  “ ((i + (r + 1 ) ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i (r + 1 ) id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i (r + 1 ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_written_2: (@list Z)) (len: Z) (i: Z) (j: Z) (ret: Z) (r: Z) (id: Z) (limit: Z) (mirror: Z) (maxLen: Z) (maxId: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i < len)) (PreH11 : (j = 0)) (PreH12 : (ret = 0)) (PreH13 : (1 <= r)) (PreH14 : (0 <= id)) (PreH15 : (id < len)) (PreH16 : (0 <= limit)) (PreH17 : (limit <= len)) (PreH18 : (0 <= mirror)) (PreH19 : (mirror < len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : (0 < (i - r ))) (PreH25 : ((i + r ) < len)) (PreH26 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH27 : ((Zlength (p_written_2)) = (i + 1 ))) (PreH28 : (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen )) (PreH29 : (ExpansionAfterMatch s2_full_2 len i r )) ,
  (IntArray.full ( &( "p" ) ) (i + 1 ) (replace_Znth (i) ((r + 1 )) (p_written_2)) )
|--
  EX (p_written: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= (r + 1 )) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - (r + 1 ) )) ” 
  &&  “ ((i + (r + 1 ) ) <= len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full_2 len p_written i (r + 1 ) id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full_2 len i (r + 1 ) ) ”
  &&  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
).

Definition longestPalindrom_entail_wit_10_1 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_next: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= (r - 1 )) ” 
  &&  “ ((r - 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_next)) = (i + 1 )) ” 
  &&  “ (ManacherLoopState str s2_full len p_next (i + 1 ) i (i + r ) i (r - 1 ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_next )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  TT && emp 
|--
  “ (ManacherLoopState str s2_full_2 ((2 * n_pre ) + 2 ) p_written (i + 1 ) i (i + r ) i (r - 1 ) ) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_10_1_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  (ManacherLoopState str s2_full_2 ((2 * n_pre ) + 2 ) p_written (i + 1 ) i (i + r ) i (r - 1 ) )
.

Definition longestPalindrom_entail_wit_10_2 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_next: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= (r - 1 )) ” 
  &&  “ ((r - 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_next)) = (i + 1 )) ” 
  &&  “ (ManacherLoopState str s2_full len p_next (i + 1 ) id limit i (r - 1 ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_next )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  TT && emp 
|--
  “ (ManacherLoopState str s2_full_2 ((2 * n_pre ) + 2 ) p_written (i + 1 ) id limit i (r - 1 ) ) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_10_2_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen < (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  (ManacherLoopState str s2_full_2 ((2 * n_pre ) + 2 ) p_written (i + 1 ) id limit i (r - 1 ) )
.

Definition longestPalindrom_entail_wit_10_3 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_next: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_next)) = (i + 1 )) ” 
  &&  “ (ManacherLoopState str s2_full len p_next (i + 1 ) i (i + r ) maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_next )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  TT && emp 
|--
  “ (ManacherLoopState str s2_full_2 ((2 * n_pre ) + 2 ) p_written (i + 1 ) i (i + r ) maxId maxLen ) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_10_3_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) > limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  (ManacherLoopState str s2_full_2 ((2 * n_pre ) + 2 ) p_written (i + 1 ) i (i + r ) maxId maxLen )
.

Definition longestPalindrom_entail_wit_10_4 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_next: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_next)) = (i + 1 )) ” 
  &&  “ (ManacherLoopState str s2_full len p_next (i + 1 ) id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_next )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  TT && emp 
|--
  “ (ManacherLoopState str s2_full_2 ((2 * n_pre ) + 2 ) p_written (i + 1 ) id limit maxId maxLen ) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_10_4_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (maxLen >= (r - 1 ))) (PreH2 : ((i + r ) <= limit)) (PreH3 : ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0))) (PreH4 : (0 <= ((string_length (str)) + 1 ))) (PreH5 : (valid_string str )) (PreH6 : (AlnumString str )) (PreH7 : ((string_length (str)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (len = ((2 * n_pre ) + 2 ))) (PreH11 : (len <= 2002)) (PreH12 : (1 <= i)) (PreH13 : (i < len)) (PreH14 : (j = 0)) (PreH15 : (ret = 0)) (PreH16 : (1 <= r)) (PreH17 : (0 <= id)) (PreH18 : (id < len)) (PreH19 : (0 <= limit)) (PreH20 : (limit <= len)) (PreH21 : (0 <= mirror)) (PreH22 : (mirror < len)) (PreH23 : (0 <= maxLen)) (PreH24 : (maxLen <= n_pre)) (PreH25 : (0 <= maxId)) (PreH26 : (maxId < len)) (PreH27 : (0 <= (i - r ))) (PreH28 : ((i + r ) <= len)) (PreH29 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH30 : ((Zlength (p_written)) = (i + 1 ))) (PreH31 : (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen )) (PreH32 : (ExpansionCandidate s2_full_2 len i r )) ,
  (ManacherLoopState str s2_full_2 ((2 * n_pre ) + 2 ) p_written (i + 1 ) id limit maxId maxLen )
.

Definition longestPalindrom_entail_wit_11 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_next: (@list Z)) (len: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (maxLen: Z) (maxId: Z) (limit: Z) (id: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (len <= 2002)) (PreH8 : (1 <= i)) (PreH9 : (i <= len)) (PreH10 : (j = 0)) (PreH11 : (r = 0)) (PreH12 : (mirror = 0)) (PreH13 : (ret = 0)) (PreH14 : (0 <= maxLen)) (PreH15 : (maxLen <= n_pre)) (PreH16 : (0 <= maxId)) (PreH17 : (maxId < len)) (PreH18 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH19 : ((Zlength (p_next)) = i)) (PreH20 : (ManacherLoopState str s2_full_2 len p_next i id limit maxId maxLen )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_next )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  EX (p_cur: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_next: (@list Z)) (len: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (maxLen: Z) (maxId: Z) (limit: Z) (id: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i <= len)) (PreH11 : (j = 0)) (PreH12 : (r = 0)) (PreH13 : (mirror = 0)) (PreH14 : (ret = 0)) (PreH15 : (0 <= maxLen)) (PreH16 : (maxLen <= n_pre)) (PreH17 : (0 <= maxId)) (PreH18 : (maxId < len)) (PreH19 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH20 : ((Zlength (p_next)) = i)) (PreH21 : (ManacherLoopState str s2_full_2 len p_next i id limit maxId maxLen )) ,
  TT && emp 
|--
  “ (limit <= ((2 * n_pre ) + 2 )) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (id < ((2 * n_pre ) + 2 )) ” 
  &&  “ (0 <= id) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_11_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_next: (@list Z)) (len: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (maxLen: Z) (maxId: Z) (limit: Z) (id: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i <= len)) (PreH11 : (j = 0)) (PreH12 : (r = 0)) (PreH13 : (mirror = 0)) (PreH14 : (ret = 0)) (PreH15 : (0 <= maxLen)) (PreH16 : (maxLen <= n_pre)) (PreH17 : (0 <= maxId)) (PreH18 : (maxId < len)) (PreH19 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH20 : ((Zlength (p_next)) = i)) (PreH21 : (ManacherLoopState str s2_full_2 len p_next i id limit maxId maxLen )) ,
  (limit <= ((2 * n_pre ) + 2 ))
.

Definition longestPalindrom_entail_wit_11_split_goal_2 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_next: (@list Z)) (len: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (maxLen: Z) (maxId: Z) (limit: Z) (id: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i <= len)) (PreH11 : (j = 0)) (PreH12 : (r = 0)) (PreH13 : (mirror = 0)) (PreH14 : (ret = 0)) (PreH15 : (0 <= maxLen)) (PreH16 : (maxLen <= n_pre)) (PreH17 : (0 <= maxId)) (PreH18 : (maxId < len)) (PreH19 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH20 : ((Zlength (p_next)) = i)) (PreH21 : (ManacherLoopState str s2_full_2 len p_next i id limit maxId maxLen )) ,
  (0 <= limit)
.

Definition longestPalindrom_entail_wit_11_split_goal_3 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_next: (@list Z)) (len: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (maxLen: Z) (maxId: Z) (limit: Z) (id: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i <= len)) (PreH11 : (j = 0)) (PreH12 : (r = 0)) (PreH13 : (mirror = 0)) (PreH14 : (ret = 0)) (PreH15 : (0 <= maxLen)) (PreH16 : (maxLen <= n_pre)) (PreH17 : (0 <= maxId)) (PreH18 : (maxId < len)) (PreH19 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH20 : ((Zlength (p_next)) = i)) (PreH21 : (ManacherLoopState str s2_full_2 len p_next i id limit maxId maxLen )) ,
  (id < ((2 * n_pre ) + 2 ))
.

Definition longestPalindrom_entail_wit_11_split_goal_4 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_next: (@list Z)) (len: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (maxLen: Z) (maxId: Z) (limit: Z) (id: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i <= len)) (PreH11 : (j = 0)) (PreH12 : (r = 0)) (PreH13 : (mirror = 0)) (PreH14 : (ret = 0)) (PreH15 : (0 <= maxLen)) (PreH16 : (maxLen <= n_pre)) (PreH17 : (0 <= maxId)) (PreH18 : (maxId < len)) (PreH19 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH20 : ((Zlength (p_next)) = i)) (PreH21 : (ManacherLoopState str s2_full_2 len p_next i id limit maxId maxLen )) ,
  (0 <= id)
.

Definition longestPalindrom_entail_wit_12 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (i >= len)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i <= len)) (PreH11 : (j = 0)) (PreH12 : (r = 0)) (PreH13 : (mirror = 0)) (PreH14 : (ret = 0)) (PreH15 : (0 <= id)) (PreH16 : (id < len)) (PreH17 : (0 <= limit)) (PreH18 : (limit <= len)) (PreH19 : (0 <= maxLen)) (PreH20 : (maxLen <= n_pre)) (PreH21 : (0 <= maxId)) (PreH22 : (maxId < len)) (PreH23 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH24 : ((Zlength (p_cur)) = i)) (PreH25 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out_pre: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) = (maxId - maxLen )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (out_pre = (@nil Z)) ” 
  &&  “ (OutputCopyPrefix s2_full out_pre (maxId - maxLen ) (maxId - maxLen ) 0 ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= len)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i <= len)) (PreH12 : (j = 0)) (PreH13 : (r = 0)) (PreH14 : (mirror = 0)) (PreH15 : (ret = 0)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH25 : ((Zlength (p_cur)) = i)) (PreH26 : (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen )) ,
  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
|--
  EX (p_done: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full_2 (@nil Z) (maxId - maxLen ) (maxId - maxLen ) 0 ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_done len id limit maxId maxLen ) ”
  &&  (IntArray.seg ( &( "p" ) ) 0 len p_done )
).

Definition longestPalindrom_entail_wit_13 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_done_2: (@list Z)) (out_pre: (@list Z)) (len: Z) (maxLen: Z) (maxId: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (limit: Z) (id: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (len <= 2002)) (PreH8 : (1 <= maxLen)) (PreH9 : (0 <= maxLen)) (PreH10 : (maxLen <= n_pre)) (PreH11 : (0 <= (maxId - maxLen ))) (PreH12 : ((maxId + maxLen ) < len)) (PreH13 : (i = (maxId - maxLen ))) (PreH14 : (j = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : (out_pre = (@nil Z))) (PreH19 : (OutputCopyPrefix s2_full_2 out_pre (maxId - maxLen ) i j )) (PreH20 : forall (cur_2: Z) , ((((maxId - maxLen ) <= cur_2) /\ (cur_2 <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur_2 maxLen ))) (PreH21 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH22 : ((Zlength (p_done_2)) = len)) (PreH23 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out_prefix: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_done_2: (@list Z)) (out_pre: (@list Z)) (len: Z) (maxLen: Z) (maxId: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (limit: Z) (id: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= maxLen)) (PreH10 : (0 <= maxLen)) (PreH11 : (maxLen <= n_pre)) (PreH12 : (0 <= (maxId - maxLen ))) (PreH13 : ((maxId + maxLen ) < len)) (PreH14 : (i = (maxId - maxLen ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : (out_pre = (@nil Z))) (PreH20 : (OutputCopyPrefix s2_full_2 out_pre (maxId - maxLen ) i j )) (PreH21 : forall (cur_2: Z) , ((((maxId - maxLen ) <= cur_2) /\ (cur_2 <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur_2 maxLen ))) (PreH22 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH23 : ((Zlength (p_done_2)) = len)) (PreH24 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  TT && emp 
|--
  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen )) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_done_2: (@list Z)) (out_pre: (@list Z)) (len: Z) (maxLen: Z) (maxId: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (limit: Z) (id: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= maxLen)) (PreH10 : (0 <= maxLen)) (PreH11 : (maxLen <= n_pre)) (PreH12 : (0 <= (maxId - maxLen ))) (PreH13 : ((maxId + maxLen ) < len)) (PreH14 : (i = (maxId - maxLen ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : (out_pre = (@nil Z))) (PreH20 : (OutputCopyPrefix s2_full_2 out_pre (maxId - maxLen ) i j )) (PreH21 : forall (cur_2: Z) , ((((maxId - maxLen ) <= cur_2) /\ (cur_2 <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur_2 maxLen ))) (PreH22 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH23 : ((Zlength (p_done_2)) = len)) (PreH24 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen ))
.

Definition longestPalindrom_entail_wit_14_1 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full_2 0) <> 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_done_2)) = len)) (PreH27 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  (CharArray.full output_pre (j + 1 ) (app (out_prefix_2) ((cons ((Znth (i - 0 ) s2_full_2 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out_prefix: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) (i + 1 ) (j + 1 ) ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre (j + 1 ) out_prefix )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full_2 0) <> 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_done_2)) = len)) (PreH27 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  TT && emp 
|--
  “ (OutputCopyPrefix s2_full_2 (app (out_prefix_2) ((cons ((Znth (i - 0 ) s2_full_2 0)) ((@nil Z))))) (maxId - maxLen ) (i + 1 ) (j + 1 ) ) ” 
  &&  “ ((j + 1 ) <= maxLen) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_14_1_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full_2 0) <> 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_done_2)) = len)) (PreH27 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  (OutputCopyPrefix s2_full_2 (app (out_prefix_2) ((cons ((Znth (i - 0 ) s2_full_2 0)) ((@nil Z))))) (maxId - maxLen ) (i + 1 ) (j + 1 ) )
.

Definition longestPalindrom_entail_wit_14_1_split_goal_2 := 
forall (n_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full_2 0) <> 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_done_2)) = len)) (PreH27 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  ((j + 1 ) <= maxLen)
.

Definition longestPalindrom_entail_wit_14_2 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full_2 0) = 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_done_2)) = len)) (PreH27 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix_2 )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out_prefix: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) (i + 1 ) j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full_2 0) = 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_done_2)) = len)) (PreH27 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  TT && emp 
|--
  “ (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) (i + 1 ) j ) ”
  &&  emp
).

Definition longestPalindrom_entail_wit_14_2_split_goal_1 := 
forall (n_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full_2 0) = 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_done_2)) = len)) (PreH27 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) (i + 1 ) j )
.

Definition longestPalindrom_entail_wit_15 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i > (maxId + maxLen ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= maxLen)) (PreH11 : (0 <= maxLen)) (PreH12 : (maxLen <= n_pre)) (PreH13 : (0 <= (maxId - maxLen ))) (PreH14 : ((maxId + maxLen ) < len)) (PreH15 : ((maxId - maxLen ) <= i)) (PreH16 : (i <= ((maxId + maxLen ) + 1 ))) (PreH17 : (0 <= j)) (PreH18 : (j <= maxLen)) (PreH19 : (r = 0)) (PreH20 : (mirror = 0)) (PreH21 : (ret = 0)) (PreH22 : (OutputCopyPrefix s2_full_2 out_prefix (maxId - maxLen ) i j )) (PreH23 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen ))) (PreH24 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH25 : ((Zlength (p_done_2)) = len)) (PreH26 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  (CharArray.full output_pre (j + 1 ) (app (out_prefix) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (maxLen = maxLen) ” 
  &&  “ (i = ((maxId + maxLen ) + 1 )) ” 
  &&  “ (j = maxLen) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (OutputCopyDone str s2_full out len maxId maxLen maxLen ) ” 
  &&  “ (LongestPalindromeResult str out maxLen ) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre (maxLen + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg output_pre (maxLen + 1 ) (n_pre + 1 ) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  (IntArray.undef_full ( &( "p" ) ) 2003 )
) \/
(
forall (output_pre: Z) (n_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : (0 <= (j + 1 ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i > (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full_2 out_prefix (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full_2)) = (len + 1 ))) (PreH26 : ((Zlength (p_done_2)) = len)) (PreH27 : (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen )) ,
  (CharArray.full output_pre (j + 1 ) (app (out_prefix) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (i = ((maxId + maxLen ) + 1 )) ” 
  &&  “ (j = maxLen) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (OutputCopyDone str s2_full out len maxId maxLen maxLen ) ” 
  &&  “ (LongestPalindromeResult str out maxLen ) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ”
  &&  (CharArray.full output_pre (maxLen + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg output_pre (maxLen + 1 ) (n_pre + 1 ) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  (IntArray.undef_full ( &( "p" ) ) 2003 )
).

Definition longestPalindrom_return_wit_1 := 
(
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_done: (@list Z)) (out_2: (@list Z)) (len: Z) (ret: Z) (maxLen: Z) (i: Z) (maxId: Z) (j: Z) (id: Z) (limit: Z) (r: Z) (mirror: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (ret = maxLen)) (PreH8 : (i = ((maxId + maxLen ) + 1 ))) (PreH9 : (j = ret)) (PreH10 : (0 <= id)) (PreH11 : (id < len)) (PreH12 : (0 <= limit)) (PreH13 : (limit <= len)) (PreH14 : (0 <= maxId)) (PreH15 : (maxId < len)) (PreH16 : (1 <= maxLen)) (PreH17 : (0 <= maxLen)) (PreH18 : (maxLen <= n_pre)) (PreH19 : (r = 0)) (PreH20 : (mirror = 0)) (PreH21 : (1 <= ret)) (PreH22 : (ret <= n_pre)) (PreH23 : (OutputCopyDone str s2_full out_2 len maxId maxLen ret )) (PreH24 : (LongestPalindromeResult str out_2 ret )) (PreH25 : ((Zlength (s2_full)) = (len + 1 ))) (PreH26 : ((Zlength (p_done)) = len)) ,
  (store_string s_pre str )
  **  (CharArray.full output_pre (ret + 1 ) (app (out_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg output_pre (ret + 1 ) (n_pre + 1 ) )
|--
  EX (out: (@list Z)) ,
  “ (LongestPalindromeResult str out ret ) ” 
  &&  “ (1 <= ret) ” 
  &&  “ (ret <= n_pre) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre (ret + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg output_pre (ret + 1 ) (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_done: (@list Z)) (out_2: (@list Z)) (len: Z) (ret: Z) (maxLen: Z) (i: Z) (maxId: Z) (j: Z) (id: Z) (limit: Z) (r: Z) (mirror: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (ret = maxLen)) (PreH9 : (i = ((maxId + maxLen ) + 1 ))) (PreH10 : (j = ret)) (PreH11 : (0 <= id)) (PreH12 : (id < len)) (PreH13 : (0 <= limit)) (PreH14 : (limit <= len)) (PreH15 : (0 <= maxId)) (PreH16 : (maxId < len)) (PreH17 : (1 <= maxLen)) (PreH18 : (0 <= maxLen)) (PreH19 : (maxLen <= n_pre)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (1 <= ret)) (PreH23 : (ret <= n_pre)) (PreH24 : (OutputCopyDone str s2_full out_2 len maxId maxLen ret )) (PreH25 : (LongestPalindromeResult str out_2 ret )) (PreH26 : ((Zlength (s2_full)) = (len + 1 ))) (PreH27 : ((Zlength (p_done)) = len)) ,
  TT && emp 
|--
  EX (out: (@list Z)) ,
  “ ((app (out_2) ((cons (0) ((@nil Z))))) = (app (out) ((cons (0) ((@nil Z)))))) ” 
  &&  “ (LongestPalindromeResult str out maxLen ) ”
  &&  emp
).

Definition longestPalindrom_partial_solve_wit_1 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) ,
  (IntArray.undef_full ( &( "p" ) ) 2003 )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (((( &( "p" ) ) + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
.

Definition longestPalindrom_partial_solve_wit_2 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) ,
  (((( &( "p" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (((( &( "s2" ) ) + (0 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg ( &( "s2" ) ) 1 2003 )
  **  (((( &( "p" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
.

Definition longestPalindrom_partial_solve_wit_3 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (((( &( "s2" ) ) + (((2 * i ) + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_missing_i ( &( "s2" ) ) ((2 * i ) + 1 ) ((2 * i ) + 1 ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_partial_solve_wit_4 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (c_string (str)) 0))
  **  (CharArray.missing_i s_pre i 0 ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_partial_solve_wit_5 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (((( &( "s2" ) ) + (((2 * i ) + 2 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i ( &( "s2" ) ) ((2 * i ) + 2 ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_partial_solve_wit_6 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (j = 0)) (PreH10 : (len = 0)) (PreH11 : (id = 0)) (PreH12 : (limit = 0)) (PreH13 : (maxLen = 0)) (PreH14 : (maxId = 0)) (PreH15 : (r = 0)) (PreH16 : (mirror = 0)) (PreH17 : (ret = 0)) (PreH18 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH19 : ((Zlength (p_pre)) = 1)) (PreH20 : (ManacherTransformedPrefix str s2_pre i )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (((( &( "s2" ) ) + (((2 * i ) + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_missing_i ( &( "s2" ) ) ((2 * i ) + 1 ) ((2 * i ) + 1 ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_partial_solve_wit_7 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (j = 0)) (PreH11 : (len = 0)) (PreH12 : (id = 0)) (PreH13 : (limit = 0)) (PreH14 : (maxLen = 0)) (PreH15 : (maxId = 0)) (PreH16 : (r = 0)) (PreH17 : (mirror = 0)) (PreH18 : (ret = 0)) (PreH19 : ((Zlength (s2_pre)) = ((2 * i ) + 1 ))) (PreH20 : ((Zlength (p_pre)) = 1)) (PreH21 : (ManacherTransformedPrefix str s2_pre i )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (((( &( "s2" ) ) + (((2 * i ) + 2 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i ( &( "s2" ) ) ((2 * i ) + 2 ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_partial_solve_wit_8 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (len <= 2002)) (PreH8 : (1 <= i)) (PreH9 : (i < len)) (PreH10 : (0 <= mirror)) (PreH11 : (mirror < i)) (PreH12 : (mirror = ((2 * id ) - i ))) (PreH13 : (j = 0)) (PreH14 : (r = 0)) (PreH15 : (ret = 0)) (PreH16 : (i < limit)) (PreH17 : (limit <= len)) (PreH18 : ((Zlength (s2_full)) = (len + 1 ))) (PreH19 : ((Zlength (p_cur)) = i)) (PreH20 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (((( &( "p" ) ) + (mirror * sizeof(INT)))) # Int  |-> (Znth (mirror - 0 ) p_cur 0))
  **  (IntArray.missing_i ( &( "p" ) ) mirror 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
.

Definition longestPalindrom_partial_solve_wit_9 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((Znth (mirror - 0 ) p_cur 0) < (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (((( &( "p" ) ) + (mirror * sizeof(INT)))) # Int  |-> (Znth (mirror - 0 ) p_cur 0))
  **  (IntArray.missing_i ( &( "p" ) ) mirror 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
.

Definition longestPalindrom_partial_solve_wit_10 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) < (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((Znth (mirror - 0 ) p_cur 0) < (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (((( &( "p" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
.

Definition longestPalindrom_partial_solve_wit_11 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) (PreH1 : ((Znth (mirror - 0 ) p_cur 0) >= (limit - i ))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i < len)) (PreH12 : (0 <= mirror)) (PreH13 : (mirror < i)) (PreH14 : (mirror = ((2 * id ) - i ))) (PreH15 : (j = 0)) (PreH16 : (r = 0)) (PreH17 : (ret = 0)) (PreH18 : (i < limit)) (PreH19 : (limit <= len)) (PreH20 : ((Zlength (s2_full)) = (len + 1 ))) (PreH21 : ((Zlength (p_cur)) = i)) (PreH22 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((Znth (mirror - 0 ) p_cur 0) >= (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (((( &( "p" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
.

Definition longestPalindrom_partial_solve_wit_12 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (i >= limit)) (PreH2 : (i < len)) (PreH3 : (valid_string str )) (PreH4 : (AlnumString str )) (PreH5 : ((string_length (str)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (len = ((2 * n_pre ) + 2 ))) (PreH9 : (len <= 2002)) (PreH10 : (1 <= i)) (PreH11 : (i <= len)) (PreH12 : (j = 0)) (PreH13 : (r = 0)) (PreH14 : (mirror = 0)) (PreH15 : (ret = 0)) (PreH16 : (0 <= id)) (PreH17 : (id < len)) (PreH18 : (0 <= limit)) (PreH19 : (limit <= len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : ((Zlength (s2_full)) = (len + 1 ))) (PreH25 : ((Zlength (p_cur)) = i)) (PreH26 : (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= limit) ” 
  &&  “ (i < len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (((( &( "p" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
.

Definition longestPalindrom_partial_solve_wit_13 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (len <= 2002)) (PreH8 : (1 <= i)) (PreH9 : (i < len)) (PreH10 : (j = 0)) (PreH11 : (ret = 0)) (PreH12 : (1 <= r)) (PreH13 : (0 <= id)) (PreH14 : (id < len)) (PreH15 : (0 <= limit)) (PreH16 : (limit <= len)) (PreH17 : (0 <= mirror)) (PreH18 : (mirror < len)) (PreH19 : (0 <= maxLen)) (PreH20 : (maxLen <= n_pre)) (PreH21 : (0 <= maxId)) (PreH22 : (maxId < len)) (PreH23 : (0 <= (i - r ))) (PreH24 : ((i + r ) <= len)) (PreH25 : ((Zlength (s2_full)) = (len + 1 ))) (PreH26 : ((Zlength (p_written)) = (i + 1 ))) (PreH27 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH28 : (ExpansionCandidate s2_full len i r )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (((( &( "s2" ) ) + ((i + r ) * sizeof(CHAR)))) # Char  |-> (Znth ((i + r ) - 0 ) s2_full 0))
  **  (CharArray.missing_i ( &( "s2" ) ) (i + r ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_partial_solve_wit_14 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= i)) (PreH10 : (i < len)) (PreH11 : (j = 0)) (PreH12 : (ret = 0)) (PreH13 : (1 <= r)) (PreH14 : (0 <= id)) (PreH15 : (id < len)) (PreH16 : (0 <= limit)) (PreH17 : (limit <= len)) (PreH18 : (0 <= mirror)) (PreH19 : (mirror < len)) (PreH20 : (0 <= maxLen)) (PreH21 : (maxLen <= n_pre)) (PreH22 : (0 <= maxId)) (PreH23 : (maxId < len)) (PreH24 : (0 <= (i - r ))) (PreH25 : ((i + r ) <= len)) (PreH26 : ((Zlength (s2_full)) = (len + 1 ))) (PreH27 : ((Zlength (p_written)) = (i + 1 ))) (PreH28 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH29 : (ExpansionCandidate s2_full len i r )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (((( &( "s2" ) ) + ((i - r ) * sizeof(CHAR)))) # Char  |-> (Znth ((i - r ) - 0 ) s2_full 0))
  **  (CharArray.missing_i ( &( "s2" ) ) (i - r ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_partial_solve_wit_15 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_written: (@list Z)) (len: Z) (i: Z) (j: Z) (ret: Z) (r: Z) (id: Z) (limit: Z) (mirror: Z) (maxLen: Z) (maxId: Z) (PreH1 : (valid_string str )) (PreH2 : (AlnumString str )) (PreH3 : ((string_length (str)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (len = ((2 * n_pre ) + 2 ))) (PreH7 : (len <= 2002)) (PreH8 : (1 <= i)) (PreH9 : (i < len)) (PreH10 : (j = 0)) (PreH11 : (ret = 0)) (PreH12 : (1 <= r)) (PreH13 : (0 <= id)) (PreH14 : (id < len)) (PreH15 : (0 <= limit)) (PreH16 : (limit <= len)) (PreH17 : (0 <= mirror)) (PreH18 : (mirror < len)) (PreH19 : (0 <= maxLen)) (PreH20 : (maxLen <= n_pre)) (PreH21 : (0 <= maxId)) (PreH22 : (maxId < len)) (PreH23 : (0 < (i - r ))) (PreH24 : ((i + r ) < len)) (PreH25 : ((Zlength (s2_full)) = (len + 1 ))) (PreH26 : ((Zlength (p_written)) = (i + 1 ))) (PreH27 : (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen )) (PreH28 : (ExpansionAfterMatch s2_full len i r )) ,
  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 < (i - r )) ” 
  &&  “ ((i + r ) < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionAfterMatch s2_full len i r ) ”
  &&  (((( &( "p" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "p" ) ) i 0 (i + 1 ) p_written )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_partial_solve_wit_16 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : (i <= (maxId + maxLen ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= maxLen)) (PreH10 : (0 <= maxLen)) (PreH11 : (maxLen <= n_pre)) (PreH12 : (0 <= (maxId - maxLen ))) (PreH13 : ((maxId + maxLen ) < len)) (PreH14 : ((maxId - maxLen ) <= i)) (PreH15 : (i <= ((maxId + maxLen ) + 1 ))) (PreH16 : (0 <= j)) (PreH17 : (j <= maxLen)) (PreH18 : (r = 0)) (PreH19 : (mirror = 0)) (PreH20 : (ret = 0)) (PreH21 : (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j )) (PreH22 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen ))) (PreH23 : ((Zlength (s2_full)) = (len + 1 ))) (PreH24 : ((Zlength (p_done)) = len)) (PreH25 : (ManacherLoopState str s2_full len p_done len id limit maxId maxLen )) ,
  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (((( &( "s2" ) ) + (i * sizeof(CHAR)))) # Char  |-> (Znth (i - 0 ) s2_full 0))
  **  (CharArray.missing_i ( &( "s2" ) ) i 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Definition longestPalindrom_partial_solve_wit_17 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full 0) <> 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full)) = (len + 1 ))) (PreH26 : ((Zlength (p_done)) = len)) (PreH27 : (ManacherLoopState str s2_full len p_done len id limit maxId maxLen )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((Znth (i - 0 ) s2_full 0) <> 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (((( &( "s2" ) ) + (i * sizeof(CHAR)))) # Char  |-> (Znth (i - 0 ) s2_full 0))
  **  (CharArray.missing_i ( &( "s2" ) ) i 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Definition longestPalindrom_partial_solve_wit_18 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : ((Znth (i - 0 ) s2_full 0) <> 35)) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (i <= (maxId + maxLen ))) (PreH4 : (valid_string str )) (PreH5 : (AlnumString str )) (PreH6 : ((string_length (str)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (len = ((2 * n_pre ) + 2 ))) (PreH10 : (len <= 2002)) (PreH11 : (1 <= maxLen)) (PreH12 : (0 <= maxLen)) (PreH13 : (maxLen <= n_pre)) (PreH14 : (0 <= (maxId - maxLen ))) (PreH15 : ((maxId + maxLen ) < len)) (PreH16 : ((maxId - maxLen ) <= i)) (PreH17 : (i <= ((maxId + maxLen ) + 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= maxLen)) (PreH20 : (r = 0)) (PreH21 : (mirror = 0)) (PreH22 : (ret = 0)) (PreH23 : (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j )) (PreH24 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen ))) (PreH25 : ((Zlength (s2_full)) = (len + 1 ))) (PreH26 : ((Zlength (p_done)) = len)) (PreH27 : (ManacherLoopState str s2_full len p_done len id limit maxId maxLen )) ,
  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((Znth (i - 0 ) s2_full 0) <> 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (((output_pre + (j * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i output_pre j j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Definition longestPalindrom_partial_solve_wit_19 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) (PreH1 : (i > (maxId + maxLen ))) (PreH2 : (valid_string str )) (PreH3 : (AlnumString str )) (PreH4 : ((string_length (str)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (len = ((2 * n_pre ) + 2 ))) (PreH8 : (len <= 2002)) (PreH9 : (1 <= maxLen)) (PreH10 : (0 <= maxLen)) (PreH11 : (maxLen <= n_pre)) (PreH12 : (0 <= (maxId - maxLen ))) (PreH13 : ((maxId + maxLen ) < len)) (PreH14 : ((maxId - maxLen ) <= i)) (PreH15 : (i <= ((maxId + maxLen ) + 1 ))) (PreH16 : (0 <= j)) (PreH17 : (j <= maxLen)) (PreH18 : (r = 0)) (PreH19 : (mirror = 0)) (PreH20 : (ret = 0)) (PreH21 : (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j )) (PreH22 : forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen ))) (PreH23 : ((Zlength (s2_full)) = (len + 1 ))) (PreH24 : ((Zlength (p_done)) = len)) (PreH25 : (ManacherLoopState str s2_full len p_done len id limit maxId maxLen )) ,
  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i > (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (((output_pre + (j * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_missing_i output_pre j j (n_pre + 1 ) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_longestPalindrom_safety_wit_1 : longestPalindrom_safety_wit_1.
Axiom proof_of_longestPalindrom_safety_wit_2 : longestPalindrom_safety_wit_2.
Axiom proof_of_longestPalindrom_safety_wit_3 : longestPalindrom_safety_wit_3.
Axiom proof_of_longestPalindrom_safety_wit_4 : longestPalindrom_safety_wit_4.
Axiom proof_of_longestPalindrom_safety_wit_5 : longestPalindrom_safety_wit_5.
Axiom proof_of_longestPalindrom_safety_wit_6 : longestPalindrom_safety_wit_6.
Axiom proof_of_longestPalindrom_safety_wit_7 : longestPalindrom_safety_wit_7.
Axiom proof_of_longestPalindrom_safety_wit_8 : longestPalindrom_safety_wit_8.
Axiom proof_of_longestPalindrom_safety_wit_9 : longestPalindrom_safety_wit_9.
Axiom proof_of_longestPalindrom_safety_wit_10 : longestPalindrom_safety_wit_10.
Axiom proof_of_longestPalindrom_safety_wit_11 : longestPalindrom_safety_wit_11.
Axiom proof_of_longestPalindrom_safety_wit_12 : longestPalindrom_safety_wit_12.
Axiom proof_of_longestPalindrom_safety_wit_13 : longestPalindrom_safety_wit_13.
Axiom proof_of_longestPalindrom_safety_wit_14 : longestPalindrom_safety_wit_14.
Axiom proof_of_longestPalindrom_safety_wit_15 : longestPalindrom_safety_wit_15.
Axiom proof_of_longestPalindrom_safety_wit_16 : longestPalindrom_safety_wit_16.
Axiom proof_of_longestPalindrom_safety_wit_17 : longestPalindrom_safety_wit_17.
Axiom proof_of_longestPalindrom_safety_wit_18 : longestPalindrom_safety_wit_18.
Axiom proof_of_longestPalindrom_safety_wit_19 : longestPalindrom_safety_wit_19.
Axiom proof_of_longestPalindrom_safety_wit_20 : longestPalindrom_safety_wit_20.
Axiom proof_of_longestPalindrom_safety_wit_21 : longestPalindrom_safety_wit_21.
Axiom proof_of_longestPalindrom_safety_wit_22 : longestPalindrom_safety_wit_22.
Axiom proof_of_longestPalindrom_safety_wit_23 : longestPalindrom_safety_wit_23.
Axiom proof_of_longestPalindrom_safety_wit_24 : longestPalindrom_safety_wit_24.
Axiom proof_of_longestPalindrom_safety_wit_25 : longestPalindrom_safety_wit_25.
Axiom proof_of_longestPalindrom_safety_wit_26 : longestPalindrom_safety_wit_26.
Axiom proof_of_longestPalindrom_safety_wit_27 : longestPalindrom_safety_wit_27.
Axiom proof_of_longestPalindrom_safety_wit_28 : longestPalindrom_safety_wit_28.
Axiom proof_of_longestPalindrom_safety_wit_29 : longestPalindrom_safety_wit_29.
Axiom proof_of_longestPalindrom_safety_wit_30 : longestPalindrom_safety_wit_30.
Axiom proof_of_longestPalindrom_safety_wit_31 : longestPalindrom_safety_wit_31.
Axiom proof_of_longestPalindrom_safety_wit_32 : longestPalindrom_safety_wit_32.
Axiom proof_of_longestPalindrom_safety_wit_33 : longestPalindrom_safety_wit_33.
Axiom proof_of_longestPalindrom_safety_wit_34 : longestPalindrom_safety_wit_34.
Axiom proof_of_longestPalindrom_safety_wit_35 : longestPalindrom_safety_wit_35.
Axiom proof_of_longestPalindrom_safety_wit_36 : longestPalindrom_safety_wit_36.
Axiom proof_of_longestPalindrom_safety_wit_37 : longestPalindrom_safety_wit_37.
Axiom proof_of_longestPalindrom_safety_wit_38 : longestPalindrom_safety_wit_38.
Axiom proof_of_longestPalindrom_safety_wit_39 : longestPalindrom_safety_wit_39.
Axiom proof_of_longestPalindrom_safety_wit_40 : longestPalindrom_safety_wit_40.
Axiom proof_of_longestPalindrom_safety_wit_41 : longestPalindrom_safety_wit_41.
Axiom proof_of_longestPalindrom_safety_wit_42 : longestPalindrom_safety_wit_42.
Axiom proof_of_longestPalindrom_safety_wit_43 : longestPalindrom_safety_wit_43.
Axiom proof_of_longestPalindrom_safety_wit_44 : longestPalindrom_safety_wit_44.
Axiom proof_of_longestPalindrom_safety_wit_45 : longestPalindrom_safety_wit_45.
Axiom proof_of_longestPalindrom_safety_wit_46 : longestPalindrom_safety_wit_46.
Axiom proof_of_longestPalindrom_safety_wit_47 : longestPalindrom_safety_wit_47.
Axiom proof_of_longestPalindrom_safety_wit_48 : longestPalindrom_safety_wit_48.
Axiom proof_of_longestPalindrom_safety_wit_49 : longestPalindrom_safety_wit_49.
Axiom proof_of_longestPalindrom_safety_wit_50 : longestPalindrom_safety_wit_50.
Axiom proof_of_longestPalindrom_safety_wit_51 : longestPalindrom_safety_wit_51.
Axiom proof_of_longestPalindrom_safety_wit_52 : longestPalindrom_safety_wit_52.
Axiom proof_of_longestPalindrom_safety_wit_53 : longestPalindrom_safety_wit_53.
Axiom proof_of_longestPalindrom_safety_wit_54 : longestPalindrom_safety_wit_54.
Axiom proof_of_longestPalindrom_safety_wit_55 : longestPalindrom_safety_wit_55.
Axiom proof_of_longestPalindrom_safety_wit_56 : longestPalindrom_safety_wit_56.
Axiom proof_of_longestPalindrom_safety_wit_57 : longestPalindrom_safety_wit_57.
Axiom proof_of_longestPalindrom_safety_wit_58 : longestPalindrom_safety_wit_58.
Axiom proof_of_longestPalindrom_safety_wit_59 : longestPalindrom_safety_wit_59.
Axiom proof_of_longestPalindrom_safety_wit_60 : longestPalindrom_safety_wit_60.
Axiom proof_of_longestPalindrom_safety_wit_61 : longestPalindrom_safety_wit_61.
Axiom proof_of_longestPalindrom_safety_wit_62 : longestPalindrom_safety_wit_62.
Axiom proof_of_longestPalindrom_safety_wit_63 : longestPalindrom_safety_wit_63.
Axiom proof_of_longestPalindrom_safety_wit_64 : longestPalindrom_safety_wit_64.
Axiom proof_of_longestPalindrom_safety_wit_65 : longestPalindrom_safety_wit_65.
Axiom proof_of_longestPalindrom_safety_wit_66 : longestPalindrom_safety_wit_66.
Axiom proof_of_longestPalindrom_safety_wit_67 : longestPalindrom_safety_wit_67.
Axiom proof_of_longestPalindrom_safety_wit_68 : longestPalindrom_safety_wit_68.
Axiom proof_of_longestPalindrom_safety_wit_69 : longestPalindrom_safety_wit_69.
Axiom proof_of_longestPalindrom_safety_wit_70 : longestPalindrom_safety_wit_70.
Axiom proof_of_longestPalindrom_safety_wit_71 : longestPalindrom_safety_wit_71.
Axiom proof_of_longestPalindrom_safety_wit_72 : longestPalindrom_safety_wit_72.
Axiom proof_of_longestPalindrom_safety_wit_73 : longestPalindrom_safety_wit_73.
Axiom proof_of_longestPalindrom_safety_wit_74 : longestPalindrom_safety_wit_74.
Axiom proof_of_longestPalindrom_entail_wit_1 : longestPalindrom_entail_wit_1.
Axiom proof_of_longestPalindrom_entail_wit_2 : longestPalindrom_entail_wit_2.
Axiom proof_of_longestPalindrom_entail_wit_3 : longestPalindrom_entail_wit_3.
Axiom proof_of_longestPalindrom_entail_wit_4 : longestPalindrom_entail_wit_4.
Axiom proof_of_longestPalindrom_entail_wit_5 : longestPalindrom_entail_wit_5.
Axiom proof_of_longestPalindrom_entail_wit_6_1 : longestPalindrom_entail_wit_6_1.
Axiom proof_of_longestPalindrom_entail_wit_6_2 : longestPalindrom_entail_wit_6_2.
Axiom proof_of_longestPalindrom_entail_wit_6_3 : longestPalindrom_entail_wit_6_3.
Axiom proof_of_longestPalindrom_entail_wit_7 : longestPalindrom_entail_wit_7.
Axiom proof_of_longestPalindrom_entail_wit_8 : longestPalindrom_entail_wit_8.
Axiom proof_of_longestPalindrom_entail_wit_9 : longestPalindrom_entail_wit_9.
Axiom proof_of_longestPalindrom_entail_wit_10_1 : longestPalindrom_entail_wit_10_1.
Axiom proof_of_longestPalindrom_entail_wit_10_2 : longestPalindrom_entail_wit_10_2.
Axiom proof_of_longestPalindrom_entail_wit_10_3 : longestPalindrom_entail_wit_10_3.
Axiom proof_of_longestPalindrom_entail_wit_10_4 : longestPalindrom_entail_wit_10_4.
Axiom proof_of_longestPalindrom_entail_wit_11 : longestPalindrom_entail_wit_11.
Axiom proof_of_longestPalindrom_entail_wit_12 : longestPalindrom_entail_wit_12.
Axiom proof_of_longestPalindrom_entail_wit_13 : longestPalindrom_entail_wit_13.
Axiom proof_of_longestPalindrom_entail_wit_14_1 : longestPalindrom_entail_wit_14_1.
Axiom proof_of_longestPalindrom_entail_wit_14_2 : longestPalindrom_entail_wit_14_2.
Axiom proof_of_longestPalindrom_entail_wit_15 : longestPalindrom_entail_wit_15.
Axiom proof_of_longestPalindrom_return_wit_1 : longestPalindrom_return_wit_1.
Axiom proof_of_longestPalindrom_partial_solve_wit_1 : longestPalindrom_partial_solve_wit_1.
Axiom proof_of_longestPalindrom_partial_solve_wit_2 : longestPalindrom_partial_solve_wit_2.
Axiom proof_of_longestPalindrom_partial_solve_wit_3 : longestPalindrom_partial_solve_wit_3.
Axiom proof_of_longestPalindrom_partial_solve_wit_4 : longestPalindrom_partial_solve_wit_4.
Axiom proof_of_longestPalindrom_partial_solve_wit_5 : longestPalindrom_partial_solve_wit_5.
Axiom proof_of_longestPalindrom_partial_solve_wit_6 : longestPalindrom_partial_solve_wit_6.
Axiom proof_of_longestPalindrom_partial_solve_wit_7 : longestPalindrom_partial_solve_wit_7.
Axiom proof_of_longestPalindrom_partial_solve_wit_8 : longestPalindrom_partial_solve_wit_8.
Axiom proof_of_longestPalindrom_partial_solve_wit_9 : longestPalindrom_partial_solve_wit_9.
Axiom proof_of_longestPalindrom_partial_solve_wit_10 : longestPalindrom_partial_solve_wit_10.
Axiom proof_of_longestPalindrom_partial_solve_wit_11 : longestPalindrom_partial_solve_wit_11.
Axiom proof_of_longestPalindrom_partial_solve_wit_12 : longestPalindrom_partial_solve_wit_12.
Axiom proof_of_longestPalindrom_partial_solve_wit_13 : longestPalindrom_partial_solve_wit_13.
Axiom proof_of_longestPalindrom_partial_solve_wit_14 : longestPalindrom_partial_solve_wit_14.
Axiom proof_of_longestPalindrom_partial_solve_wit_15 : longestPalindrom_partial_solve_wit_15.
Axiom proof_of_longestPalindrom_partial_solve_wit_16 : longestPalindrom_partial_solve_wit_16.
Axiom proof_of_longestPalindrom_partial_solve_wit_17 : longestPalindrom_partial_solve_wit_17.
Axiom proof_of_longestPalindrom_partial_solve_wit_18 : longestPalindrom_partial_solve_wit_18.
Axiom proof_of_longestPalindrom_partial_solve_wit_19 : longestPalindrom_partial_solve_wit_19.

End VC_Correct.
