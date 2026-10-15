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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P022_245B_internet_address_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) = 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "ru" ) )) # Int  |-> (-1))
  **  ((( &( "p" ) )) # Int  |-> 4)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) <> 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "ru" ) )) # Int  |-> (-1))
  **  ((( &( "p" ) )) # Int  |-> 3)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) = 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "ru" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> 4)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) = 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "ru" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> 4)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) <> 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "ru" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> 3)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) <> 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "ru" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> 3)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (plain)))) (PreH2 : (0 <= ((string_length (plain)) + 1 ))) (PreH3 : (1 <= (Zlength (plain)))) (PreH4 : ((Zlength (plain)) <= 50)) (PreH5 : (Pre plain )) (PreH6 : (valid_string plain )) (PreH7 : ((string_length (plain)) = (Zlength (plain)))) (PreH8 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (plain)))) (PreH2 : (0 <= ((string_length (plain)) + 1 ))) (PreH3 : (1 <= (Zlength (plain)))) (PreH4 : ((Zlength (plain)) <= 50)) (PreH5 : (Pre plain )) (PreH6 : (valid_string plain )) (PreH7 : ((string_length (plain)) = (Zlength (plain)))) (PreH8 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (104 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 104) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) = 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) <> 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) = 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "ru" ) )) # Int  |-> (-1))
  **  ((( &( "p" ) )) # Int  |-> 4)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((4 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (4 + 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) = 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "ru" ) )) # Int  |-> (-1))
  **  ((( &( "p" ) )) # Int  |-> 4)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) <> 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "ru" ) )) # Int  |-> (-1))
  **  ((( &( "p" ) )) # Int  |-> 3)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((3 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (3 + 1 )) ”
.

Definition solver_safety_wit_14 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) <> 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "ru" ) )) # Int  |-> (-1))
  **  ((( &( "p" ) )) # Int  |-> 3)
  **  (store_string s_pre plain )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= i)) (PreH8 : (i <= marker)) (PreH9 : ((marker + 1 ) < n)) (PreH10 : ((Znth marker plain 0) = 114)) (PreH11 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH12 : (ru = (-1))) (PreH13 : (k = 0)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= i)) (PreH8 : (i <= marker)) (PreH9 : ((marker + 1 ) < n)) (PreH10 : ((Znth marker plain 0) = 114)) (PreH11 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH12 : (ru = (-1))) (PreH13 : (k = 0)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= i)) (PreH8 : (i <= marker)) (PreH9 : ((marker + 1 ) < n)) (PreH10 : ((Znth marker plain 0) = 114)) (PreH11 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH12 : (ru = (-1))) (PreH13 : (k = 0)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= i)) (PreH8 : (i <= marker)) (PreH9 : ((marker + 1 ) < n)) (PreH10 : ((Znth marker plain 0) = 114)) (PreH11 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH12 : (ru = (-1))) (PreH13 : (k = 0)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((i + 1 ) >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= i)) (PreH9 : (i <= marker)) (PreH10 : ((marker + 1 ) < n)) (PreH11 : ((Znth marker plain 0) = 114)) (PreH12 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH13 : (ru = (-1))) (PreH14 : (k = 0)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ False ”
.

Definition solver_safety_wit_20 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((i + 1 ) >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= i)) (PreH9 : (i <= marker)) (PreH10 : ((marker + 1 ) < n)) (PreH11 : ((Znth marker plain 0) = 114)) (PreH12 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH13 : (ru = (-1))) (PreH14 : (k = 0)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ False ”
.

Definition solver_safety_wit_21 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((i + 1 ) < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= i)) (PreH9 : (i <= marker)) (PreH10 : ((marker + 1 ) < n)) (PreH11 : ((Znth marker plain 0) = 114)) (PreH12 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH13 : (ru = (-1))) (PreH14 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (114 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 114) ”
.

Definition solver_safety_wit_22 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((i + 1 ) < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= i)) (PreH9 : (i <= marker)) (PreH10 : ((marker + 1 ) < n)) (PreH11 : ((Znth marker plain 0) = 114)) (PreH12 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH13 : (ru = (-1))) (PreH14 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (114 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 114) ”
.

Definition solver_safety_wit_23 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker)) (PreH11 : ((marker + 1 ) < n)) (PreH12 : ((Znth marker plain 0) = 114)) (PreH13 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_24 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker)) (PreH11 : ((marker + 1 ) < n)) (PreH12 : ((Znth marker plain 0) = 114)) (PreH13 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_25 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker)) (PreH11 : ((marker + 1 ) < n)) (PreH12 : ((Znth marker plain 0) = 114)) (PreH13 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_26 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker)) (PreH11 : ((marker + 1 ) < n)) (PreH12 : ((Znth marker plain 0) = 114)) (PreH13 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_27 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker)) (PreH11 : ((marker + 1 ) < n)) (PreH12 : ((Znth marker plain 0) = 114)) (PreH13 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition solver_safety_wit_28 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker)) (PreH11 : ((marker + 1 ) < n)) (PreH12 : ((Znth marker plain 0) = 114)) (PreH13 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition solver_safety_wit_29 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) <> 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker)) (PreH11 : ((marker + 1 ) < n)) (PreH12 : ((Znth marker plain 0) = 114)) (PreH13 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) <> 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker)) (PreH11 : ((marker + 1 ) < n)) (PreH12 : ((Znth marker plain 0) = 114)) (PreH13 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_31 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) <> 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 3)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker)) (PreH12 : ((marker + 1 ) < n)) (PreH13 : ((Znth marker plain 0) = 114)) (PreH14 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_32 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) <> 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 4)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker)) (PreH12 : ((marker + 1 ) < n)) (PreH13 : ((Znth marker plain 0) = 114)) (PreH14 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_33 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_34 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_35 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_36 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_37 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_38 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_39 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= p)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (0 <= i)) (PreH13 : (i <= p)) (PreH14 : (k = i)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (58 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 58) ”
.

Definition solver_safety_wit_40 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= p)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (0 <= i)) (PreH13 : (i <= p)) (PreH14 : (k = i)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (58 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 58) ”
.

Definition solver_safety_wit_41 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_42 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_43 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition solver_safety_wit_44 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition solver_safety_wit_45 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (((k + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k + 1 ) + 1 )) ”
.

Definition solver_safety_wit_46 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (((k + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k + 1 ) + 1 )) ”
.

Definition solver_safety_wit_47 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition solver_safety_wit_48 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition solver_safety_wit_49 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((((k + 1 ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((k + 1 ) + 1 ) + 1 )) ”
.

Definition solver_safety_wit_50 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((((k + 1 ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((k + 1 ) + 1 ) + 1 )) ”
.

Definition solver_safety_wit_51 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_52 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_53 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_54 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_55 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= ru)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (p <= i)) (PreH13 : (i <= ru)) (PreH14 : (k = (i + 3 ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition solver_safety_wit_56 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= ru)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (p <= i)) (PreH13 : (i <= ru)) (PreH14 : (k = (i + 3 ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition solver_safety_wit_57 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_58 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_59 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (114 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 114) ”
.

Definition solver_safety_wit_60 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (114 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 114) ”
.

Definition solver_safety_wit_61 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (((k + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k + 1 ) + 1 )) ”
.

Definition solver_safety_wit_62 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (((k + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k + 1 ) + 1 )) ”
.

Definition solver_safety_wit_63 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition solver_safety_wit_64 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition solver_safety_wit_65 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z)))))) ((cons (117) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((((k + 1 ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((k + 1 ) + 1 ) + 1 )) ”
.

Definition solver_safety_wit_66 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z)))))) ((cons (117) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((((k + 1 ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((k + 1 ) + 1 ) + 1 )) ”
.

Definition solver_safety_wit_67 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = (ru + 6 ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ ((ru + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ru + 2 )) ”
.

Definition solver_safety_wit_68 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = (ru + 6 ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ ((ru + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ru + 2 )) ”
.

Definition solver_safety_wit_69 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = (ru + 6 ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_70 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = (ru + 6 ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_71 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition solver_safety_wit_72 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition solver_safety_wit_73 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_74 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_75 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((ru + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ru + 2 )) ”
.

Definition solver_safety_wit_76 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_77 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((ru + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ru + 2 )) ”
.

Definition solver_safety_wit_78 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_79 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 2 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : ((ru + 2 ) <= i)) (PreH14 : (i <= n)) (PreH15 : (k = (i + 5 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_80 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 2 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : ((ru + 2 ) <= i)) (PreH14 : (i <= n)) (PreH15 : (k = (i + 5 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_81 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 2 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : ((ru + 2 ) <= i)) (PreH14 : (i <= n)) (PreH15 : (k = (i + 5 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_82 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 2 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : ((ru + 2 ) <= i)) (PreH14 : (i <= n)) (PreH15 : (k = (i + 5 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_83 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (address: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((p + 1 ) <= ru)) (PreH7 : ((ru + 1 ) < n)) (PreH8 : (Spec plain address )) (PreH9 : (k = (Zlength (address)))) (PreH10 : (0 <= k)) (PreH11 : (k < 72)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k address )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_84 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (address: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((p + 1 ) <= ru)) (PreH7 : ((ru + 1 ) < n)) (PreH8 : (Spec plain address )) (PreH9 : (k = (Zlength (address)))) (PreH10 : (0 <= k)) (PreH11 : (k < 72)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ru" ) )) # Int  |-> ru)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k address )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (PreH1 : (1 <= (Zlength (plain)))) (PreH2 : ((Zlength (plain)) <= 50)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (plain)))) -> ((97 <= (Znth i plain 0)) /\ ((Znth i plain 0) <= 122)))) (PreH4 : (Pre plain )) ,
  (CharArray.full s_pre ((Zlength (plain)) + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (1 <= (Zlength (plain))) ” 
  &&  “ ((Zlength (plain)) <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (valid_string plain ) ” 
  &&  “ ((string_length (plain)) = (Zlength (plain))) ” 
  &&  “ ((string_length (plain)) < INT_MAX) ”
  &&  (store_string s_pre plain )
  **  (CharArray.undef_full out_pre 72 )
) \/
(
forall (s_pre: Z) (plain: (@list Z)) (PreH1 : (0 <= ((Zlength (plain)) + 1 ))) (PreH2 : (1 <= (Zlength (plain)))) (PreH3 : ((Zlength (plain)) <= 50)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (plain)))) -> ((97 <= (Znth i plain 0)) /\ ((Znth i plain 0) <= 122)))) (PreH5 : (Pre plain )) ,
  (CharArray.full s_pre ((Zlength (plain)) + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((string_length (plain)) < INT_MAX) ” 
  &&  “ ((string_length (plain)) = (Zlength (plain))) ” 
  &&  “ (valid_string plain ) ”
  &&  (CharArray.full s_pre ((string_length (plain)) + 1 ) (c_string (plain)) )
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (s_pre: Z) (plain: (@list Z)) (PreH1 : (0 <= ((Zlength (plain)) + 1 ))) (PreH2 : (1 <= (Zlength (plain)))) (PreH3 : ((Zlength (plain)) <= 50)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (plain)))) -> ((97 <= (Znth i plain 0)) /\ ((Znth i plain 0) <= 122)))) (PreH5 : (Pre plain )) ,
  (CharArray.full s_pre ((Zlength (plain)) + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((string_length (plain)) < INT_MAX) ”
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (s_pre: Z) (plain: (@list Z)) (PreH1 : (0 <= ((Zlength (plain)) + 1 ))) (PreH2 : (1 <= (Zlength (plain)))) (PreH3 : ((Zlength (plain)) <= 50)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (plain)))) -> ((97 <= (Znth i plain 0)) /\ ((Znth i plain 0) <= 122)))) (PreH5 : (Pre plain )) ,
  (CharArray.full s_pre ((Zlength (plain)) + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ ((string_length (plain)) = (Zlength (plain))) ”
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (s_pre: Z) (plain: (@list Z)) (PreH1 : (0 <= ((Zlength (plain)) + 1 ))) (PreH2 : (1 <= (Zlength (plain)))) (PreH3 : ((Zlength (plain)) <= 50)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (plain)))) -> ((97 <= (Znth i plain 0)) /\ ((Znth i plain 0) <= 122)))) (PreH5 : (Pre plain )) ,
  (CharArray.full s_pre ((Zlength (plain)) + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (valid_string plain ) ”
.

Definition solver_entail_wit_1_split_goal_spatial := 
forall (s_pre: Z) (plain: (@list Z)) (PreH1 : (0 <= ((Zlength (plain)) + 1 ))) (PreH2 : (1 <= (Zlength (plain)))) (PreH3 : ((Zlength (plain)) <= 50)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (plain)))) -> ((97 <= (Znth i plain 0)) /\ ((Znth i plain 0) <= 122)))) (PreH5 : (Pre plain )) ,
  (CharArray.full s_pre ((Zlength (plain)) + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  (CharArray.full s_pre ((string_length (plain)) + 1 ) (c_string (plain)) )
.

Definition solver_entail_wit_2_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) = 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  (store_string s_pre plain )
  **  (CharArray.undef_full out_pre 72 )
|--
  EX (marker: Z) ,
  “ (retval = (Zlength (plain))) ” 
  &&  “ (1 <= retval) ” 
  &&  “ (retval <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (4 = 4) ” 
  &&  “ ((sublist (0) (4) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((4 + 1 ) <= (4 + 1 )) ” 
  &&  “ ((4 + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < retval) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (0 = 0) ”
  &&  (CharArray.full s_pre (retval + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
) \/
(
forall (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) = 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (plain)) + 1 ) (c_string (plain)) )
|--
  EX (marker: Z) ,
  “ (retval = (Zlength (plain))) ” 
  &&  “ (1 <= retval) ” 
  &&  “ (retval <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ ((sublist (0) (4) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((4 + 1 ) <= (4 + 1 )) ” 
  &&  “ ((4 + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < retval) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ”
  &&  (CharArray.full s_pre (retval + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
).

Definition solver_entail_wit_2_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) <> 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  (store_string s_pre plain )
  **  (CharArray.undef_full out_pre 72 )
|--
  EX (marker: Z) ,
  “ (retval = (Zlength (plain))) ” 
  &&  “ (1 <= retval) ” 
  &&  “ (retval <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (3 = 3) ” 
  &&  “ ((sublist (0) (3) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((3 + 1 ) <= (3 + 1 )) ” 
  &&  “ ((3 + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < retval) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (0 = 0) ”
  &&  (CharArray.full s_pre (retval + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
) \/
(
forall (s_pre: Z) (plain: (@list Z)) (retval: Z) (PreH1 : ((Znth 0 (c_string (plain)) 0) <> 104)) (PreH2 : (retval = (string_length (plain)))) (PreH3 : (0 <= ((string_length (plain)) + 1 ))) (PreH4 : (1 <= (Zlength (plain)))) (PreH5 : ((Zlength (plain)) <= 50)) (PreH6 : (Pre plain )) (PreH7 : (valid_string plain )) (PreH8 : ((string_length (plain)) = (Zlength (plain)))) (PreH9 : ((string_length (plain)) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (plain)) + 1 ) (c_string (plain)) )
|--
  EX (marker: Z) ,
  “ (retval = (Zlength (plain))) ” 
  &&  “ (1 <= retval) ” 
  &&  “ (retval <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ ((sublist (0) (3) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((3 + 1 ) <= (3 + 1 )) ” 
  &&  “ ((3 + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < retval) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ”
  &&  (CharArray.full s_pre (retval + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
).

Definition solver_entail_wit_3_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) = 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 3)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker)) (PreH12 : ((marker + 1 ) < n)) (PreH13 : ((Znth marker plain 0) = 114)) (PreH14 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= i) ” 
  &&  “ ((i + 1 ) < n) ” 
  &&  “ ((Znth i plain 0) = 114) ” 
  &&  “ ((Znth (i + 1 ) plain 0) = 117) ” 
  &&  “ (k = 0) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) = 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 3)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker)) (PreH12 : ((marker + 1 ) < n)) (PreH13 : ((Znth marker plain 0) = 114)) (PreH14 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  TT && emp 
|--
  “ ((Znth (i + 1 ) plain 0) = 117) ” 
  &&  “ ((Znth i plain 0) = 114) ”
  &&  emp
).

Definition solver_entail_wit_3_1_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) = 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 3)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker)) (PreH12 : ((marker + 1 ) < n)) (PreH13 : ((Znth marker plain 0) = 114)) (PreH14 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  ((Znth (i + 1 ) plain 0) = 117)
.

Definition solver_entail_wit_3_1_split_goal_2 := 
forall (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) = 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 3)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker)) (PreH12 : ((marker + 1 ) < n)) (PreH13 : ((Znth marker plain 0) = 114)) (PreH14 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  ((Znth i plain 0) = 114)
.

Definition solver_entail_wit_3_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) = 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 4)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker)) (PreH12 : ((marker + 1 ) < n)) (PreH13 : ((Znth marker plain 0) = 114)) (PreH14 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= i) ” 
  &&  “ ((i + 1 ) < n) ” 
  &&  “ ((Znth i plain 0) = 114) ” 
  &&  “ ((Znth (i + 1 ) plain 0) = 117) ” 
  &&  “ (k = 0) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) = 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 4)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker)) (PreH12 : ((marker + 1 ) < n)) (PreH13 : ((Znth marker plain 0) = 114)) (PreH14 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  TT && emp 
|--
  “ ((Znth (i + 1 ) plain 0) = 117) ” 
  &&  “ ((Znth i plain 0) = 114) ”
  &&  emp
).

Definition solver_entail_wit_3_2_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) = 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 4)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker)) (PreH12 : ((marker + 1 ) < n)) (PreH13 : ((Znth marker plain 0) = 114)) (PreH14 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  ((Znth (i + 1 ) plain 0) = 117)
.

Definition solver_entail_wit_3_2_split_goal_2 := 
forall (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) = 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 4)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker)) (PreH12 : ((marker + 1 ) < n)) (PreH13 : ((Znth marker plain 0) = 114)) (PreH14 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  ((Znth i plain 0) = 114)
.

Definition solver_entail_wit_4_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker_2: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) <> 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker_2)) (PreH11 : ((marker_2 + 1 ) < n)) (PreH12 : ((Znth marker_2 plain 0) = 114)) (PreH13 : ((Znth (marker_2 + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  EX (marker: Z) ,
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < n) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ” 
  &&  “ (ru = (-1)) ” 
  &&  “ (k = 0) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (ru: Z) (marker_2: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) <> 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker_2)) (PreH11 : ((marker_2 + 1 ) < n)) (PreH12 : ((Znth marker_2 plain 0) = 114)) (PreH13 : ((Znth (marker_2 + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  TT && emp 
|--
  EX (marker: Z) ,
  “ ((4 + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < (Zlength (plain))) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ”
  &&  emp
).

Definition solver_entail_wit_4_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker_2: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) <> 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker_2)) (PreH11 : ((marker_2 + 1 ) < n)) (PreH12 : ((Znth marker_2 plain 0) = 114)) (PreH13 : ((Znth (marker_2 + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  EX (marker: Z) ,
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < n) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ” 
  &&  “ (ru = (-1)) ” 
  &&  “ (k = 0) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (ru: Z) (marker_2: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) <> 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker_2)) (PreH11 : ((marker_2 + 1 ) < n)) (PreH12 : ((Znth marker_2 plain 0) = 114)) (PreH13 : ((Znth (marker_2 + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  TT && emp 
|--
  EX (marker: Z) ,
  “ ((3 + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < (Zlength (plain))) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ”
  &&  emp
).

Definition solver_entail_wit_4_3 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker_2: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) <> 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 3)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker_2)) (PreH12 : ((marker_2 + 1 ) < n)) (PreH13 : ((Znth marker_2 plain 0) = 114)) (PreH14 : ((Znth (marker_2 + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  EX (marker: Z) ,
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < n) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ” 
  &&  “ (ru = (-1)) ” 
  &&  “ (k = 0) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (ru: Z) (marker_2: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) <> 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 3)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker_2)) (PreH12 : ((marker_2 + 1 ) < n)) (PreH13 : ((Znth marker_2 plain 0) = 114)) (PreH14 : ((Znth (marker_2 + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  TT && emp 
|--
  EX (marker: Z) ,
  “ ((3 + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < (Zlength (plain))) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ”
  &&  emp
).

Definition solver_entail_wit_4_4 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker_2: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) <> 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 4)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker_2)) (PreH12 : ((marker_2 + 1 ) < n)) (PreH13 : ((Znth marker_2 plain 0) = 114)) (PreH14 : ((Znth (marker_2 + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  EX (marker: Z) ,
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < n) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ” 
  &&  “ (ru = (-1)) ” 
  &&  “ (k = 0) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (ru: Z) (marker_2: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0) <> 117)) (PreH2 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH3 : ((i + 1 ) < n)) (PreH4 : (n = (Zlength (plain)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : (Pre plain )) (PreH8 : (p = 4)) (PreH9 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH10 : ((p + 1 ) <= i)) (PreH11 : (i <= marker_2)) (PreH12 : ((marker_2 + 1 ) < n)) (PreH13 : ((Znth marker_2 plain 0) = 114)) (PreH14 : ((Znth (marker_2 + 1 ) plain 0) = 117)) (PreH15 : (ru = (-1))) (PreH16 : (k = 0)) ,
  TT && emp 
|--
  EX (marker: Z) ,
  “ ((4 + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= marker) ” 
  &&  “ ((marker + 1 ) < (Zlength (plain))) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ”
  &&  emp
).

Definition solver_entail_wit_5_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= p) ” 
  &&  “ (k = 0) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (0) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
) \/
(
forall (out_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = 0)) ,
  TT && emp 
|--
  (CharArray.seg out_pre 0 k (sublist (0) (0) (plain)) )
).

Definition solver_entail_wit_5_1_split_goal_spatial := 
forall (out_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = 0)) ,
  TT && emp 
|--
  (CharArray.seg out_pre 0 k (sublist (0) (0) (plain)) )
.

Definition solver_entail_wit_5_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= p) ” 
  &&  “ (k = 0) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (0) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
) \/
(
forall (out_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = 0)) ,
  TT && emp 
|--
  (CharArray.seg out_pre 0 k (sublist (0) (0) (plain)) )
).

Definition solver_entail_wit_5_2_split_goal_spatial := 
forall (out_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = 0)) ,
  TT && emp 
|--
  (CharArray.seg out_pre 0 k (sublist (0) (0) (plain)) )
.

Definition solver_entail_wit_6_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= p) ” 
  &&  “ ((k + 1 ) = (i + 1 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (k + 1 ) (sublist (0) ((i + 1 )) (plain)) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (k) (plain))) ((cons ((Znth k (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (sublist (0) ((k + 1 )) (plain))) ”
  &&  emp
).

Definition solver_entail_wit_6_1_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  ((app ((sublist (0) (k) (plain))) ((cons ((Znth k (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (sublist (0) ((k + 1 )) (plain)))
.

Definition solver_entail_wit_6_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= p) ” 
  &&  “ ((k + 1 ) = (i + 1 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (k + 1 ) (sublist (0) ((i + 1 )) (plain)) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (k) (plain))) ((cons ((Znth k (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (sublist (0) ((k + 1 )) (plain))) ”
  &&  emp
).

Definition solver_entail_wit_6_2_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  ((app ((sublist (0) (k) (plain))) ((cons ((Znth k (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (sublist (0) ((k + 1 )) (plain)))
.

Definition solver_entail_wit_7_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((((k + 1 ) + 1 ) + 1 ) = (p + 3 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((sublist (0) (p) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z))))))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  TT && emp 
|--
  “ ((app ((app ((app ((sublist (0) (k) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z)))))) ((cons (47) ((@nil Z))))) = (app ((sublist (0) (3) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))))) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  ((app ((app ((app ((sublist (0) (k) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z)))))) ((cons (47) ((@nil Z))))) = (app ((sublist (0) (3) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z))))))))))
.

Definition solver_entail_wit_7_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((((k + 1 ) + 1 ) + 1 ) = (p + 3 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((sublist (0) (p) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z))))))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  TT && emp 
|--
  “ ((app ((app ((app ((sublist (0) (k) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z)))))) ((cons (47) ((@nil Z))))) = (app ((sublist (0) (4) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))))) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  ((app ((app ((app ((sublist (0) (k) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z)))))) ((cons (47) ((@nil Z))))) = (app ((sublist (0) (4) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z))))))))))
.

Definition solver_entail_wit_8_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = (p + 3 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= p) ” 
  &&  “ (p <= ru) ” 
  &&  “ (k = (p + 3 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (p) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
) \/
(
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = (p + 3 ))) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (3) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z))))))))) = (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (3) (3) (plain))))))) ”
  &&  emp
).

Definition solver_entail_wit_8_1_split_goal_1 := 
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = (p + 3 ))) ,
  ((app ((sublist (0) (3) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z))))))))) = (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (3) (3) (plain)))))))
.

Definition solver_entail_wit_8_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = (p + 3 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= p) ” 
  &&  “ (p <= ru) ” 
  &&  “ (k = (p + 3 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (p) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
) \/
(
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = (p + 3 ))) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (4) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z))))))))) = (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (4) (4) (plain))))))) ”
  &&  emp
).

Definition solver_entail_wit_8_2_split_goal_1 := 
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : ((Znth ru plain 0) = 114)) (PreH10 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH11 : (k = (p + 3 ))) ,
  ((app ((sublist (0) (4) (plain))) ((cons (58) ((cons (47) ((cons (47) ((@nil Z))))))))) = (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (4) (4) (plain)))))))
.

Definition solver_entail_wit_9_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ru) ” 
  &&  “ ((k + 1 ) = ((i + 1 ) + 3 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) ((i + 1 )) (plain)))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  TT && emp 
|--
  “ ((app ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (3) (i) (plain))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (3) ((i + 1 )) (plain))))))) ”
  &&  emp
).

Definition solver_entail_wit_9_1_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  ((app ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (3) (i) (plain))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (3) ((i + 1 )) (plain)))))))
.

Definition solver_entail_wit_9_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ru) ” 
  &&  “ ((k + 1 ) = ((i + 1 ) + 3 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) ((i + 1 )) (plain)))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  TT && emp 
|--
  “ ((app ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (4) (i) (plain))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (4) ((i + 1 )) (plain))))))) ”
  &&  emp
).

Definition solver_entail_wit_9_2_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  ((app ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (4) (i) (plain))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (4) ((i + 1 )) (plain)))))))
.

Definition solver_entail_wit_10_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z)))))) ((cons (117) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((((k + 1 ) + 1 ) + 1 ) = (ru + 6 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  TT && emp 
|--
  “ ((app ((app ((app ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (3) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z)))))) ((cons (117) ((@nil Z))))) = (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ”
  &&  emp
).

Definition solver_entail_wit_10_1_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  ((app ((app ((app ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (3) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z)))))) ((cons (117) ((@nil Z))))) = (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))))
.

Definition solver_entail_wit_10_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z)))))) ((cons (117) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((((k + 1 ) + 1 ) + 1 ) = (ru + 6 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (((k + 1 ) + 1 ) + 1 ) (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre (((k + 1 ) + 1 ) + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  TT && emp 
|--
  “ ((app ((app ((app ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (4) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z)))))) ((cons (117) ((@nil Z))))) = (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ”
  &&  emp
).

Definition solver_entail_wit_10_2_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  ((app ((app ((app ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (4) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z)))))) ((cons (117) ((@nil Z))))) = (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))))
.

Definition solver_entail_wit_11_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 2 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((ru + 2 ) <= (ru + 2 )) ” 
  &&  “ ((ru + 2 ) <= n) ” 
  &&  “ ((k + 1 ) = ((ru + 2 ) + 5 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((ru + 2 )) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  TT && emp 
|--
  “ ((app ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) = (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((ru + 2 )) (plain))))))))))))) ”
  &&  emp
).

Definition solver_entail_wit_11_1_split_goal_1 := 
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  ((app ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) = (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((ru + 2 )) (plain)))))))))))))
.

Definition solver_entail_wit_11_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 2 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((ru + 2 ) <= (ru + 2 )) ” 
  &&  “ ((ru + 2 ) <= n) ” 
  &&  “ ((k + 1 ) = ((ru + 2 ) + 5 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((ru + 2 )) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  TT && emp 
|--
  “ ((app ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) = (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((ru + 2 )) (plain))))))))))))) ”
  &&  emp
).

Definition solver_entail_wit_11_2_split_goal_1 := 
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : ((ru + 2 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (k = (ru + 6 ))) ,
  ((app ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))) ((cons (47) ((@nil Z))))) = (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((ru + 2 )) (plain)))))))))))))
.

Definition solver_entail_wit_12_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 2 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : ((ru + 2 ) <= i)) (PreH14 : (i <= n)) (PreH15 : (k = (i + 5 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 2 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((ru + 2 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ ((k + 1 ) = ((i + 1 ) + 5 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((i + 1 )) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 2 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : ((ru + 2 ) <= i)) (PreH14 : (i <= n)) (PreH15 : (k = (i + 5 ))) ,
  TT && emp 
|--
  “ ((app ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((i + 1 )) (plain))))))))))))) ”
  &&  emp
).

Definition solver_entail_wit_12_1_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 2 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : ((ru + 2 ) <= i)) (PreH14 : (i <= n)) (PreH15 : (k = (i + 5 ))) ,
  ((app ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((i + 1 )) (plain)))))))))))))
.

Definition solver_entail_wit_12_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 2 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : ((ru + 2 ) <= i)) (PreH14 : (i <= n)) (PreH15 : (k = (i + 5 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 2 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((ru + 2 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ ((k + 1 ) = ((i + 1 ) + 5 )) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((i + 1 )) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 2 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : ((ru + 2 ) <= i)) (PreH14 : (i <= n)) (PreH15 : (k = (i + 5 ))) ,
  TT && emp 
|--
  “ ((app ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((i + 1 )) (plain))))))))))))) ”
  &&  emp
).

Definition solver_entail_wit_12_2_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 2 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : ((ru + 2 ) <= i)) (PreH14 : (i <= n)) (PreH15 : (k = (i + 5 ))) ,
  ((app ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))) ((cons ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) = (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) ((i + 1 )) (plain)))))))))))))
.

Definition solver_entail_wit_13_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  EX (address: (@list Z)) ,
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ (Spec plain address ) ” 
  &&  “ (k = (Zlength (address))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 72) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k address )
  **  (CharArray.undef_seg out_pre k 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  TT && emp 
|--
  “ ((i + 5 ) = (Zlength ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))))) ” 
  &&  “ (Spec plain (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) ) ”
  &&  emp
).

Definition solver_entail_wit_13_1_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  ((i + 5 ) = (Zlength ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))))))
.

Definition solver_entail_wit_13_1_split_goal_2 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  (Spec plain (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
.

Definition solver_entail_wit_13_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  EX (address: (@list Z)) ,
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ (Spec plain address ) ” 
  &&  “ (k = (Zlength (address))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 72) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k address )
  **  (CharArray.undef_seg out_pre k 72 )
) \/
(
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  TT && emp 
|--
  “ ((i + 5 ) = (Zlength ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain))))))))))))))) ” 
  &&  “ (Spec plain (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) ) ”
  &&  emp
).

Definition solver_entail_wit_13_2_split_goal_1 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  ((i + 5 ) = (Zlength ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))))))
.

Definition solver_entail_wit_13_2_split_goal_2 := 
forall (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  (Spec plain (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
.

Definition solver_entail_wit_13_3 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  EX (address: (@list Z)) ,
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ (Spec plain address ) ” 
  &&  “ (k = (Zlength (address))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 72) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k address )
  **  (CharArray.undef_seg out_pre k 72 )
) \/
(
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  TT && emp 
|--
  “ ((ru + 6 ) = (Zlength ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))))) ” 
  &&  “ (Spec plain (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) ) ”
  &&  emp
).

Definition solver_entail_wit_13_3_split_goal_1 := 
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  ((ru + 6 ) = (Zlength ((app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))))))
.

Definition solver_entail_wit_13_3_split_goal_2 := 
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  (Spec plain (app ((sublist (0) (3) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (3) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
.

Definition solver_entail_wit_13_4 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  EX (address: (@list Z)) ,
  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ (Spec plain address ) ” 
  &&  “ (k = (Zlength (address))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 72) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k address )
  **  (CharArray.undef_seg out_pre k 72 )
) \/
(
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  TT && emp 
|--
  “ ((ru + 6 ) = (Zlength ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))))))))))) ” 
  &&  “ (Spec plain (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) ) ”
  &&  emp
).

Definition solver_entail_wit_13_4_split_goal_1 := 
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  ((ru + 6 ) = (Zlength ((app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))))))
.

Definition solver_entail_wit_13_4_split_goal_2 := 
forall (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) >= n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  (Spec plain (app ((sublist (0) (4) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (4) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
.

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (address_2: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : (Spec plain address_2 )) (PreH10 : (k = (Zlength (address_2)))) (PreH11 : (0 <= k)) (PreH12 : (k < 72)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app (address_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  EX (address: (@list Z)) ,
  “ (Spec plain address ) ”
  &&  (CharArray.full s_pre ((Zlength (plain)) + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (address)) + 1 ) (app (address) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (address)) + 1 ) 72 )
) \/
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (address_2: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : (Spec plain address_2 )) (PreH10 : (k = (Zlength (address_2)))) (PreH11 : (0 <= k)) (PreH12 : (k < 72)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app (address_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  EX (address: (@list Z)) ,
  “ (Spec plain address ) ”
  &&  (CharArray.full s_pre ((Zlength (plain)) + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (address)) + 1 ) (app (address) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (address)) + 1 ) 72 )
).

Definition solver_return_wit_2 := 
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (address_2: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : (Spec plain address_2 )) (PreH10 : (k = (Zlength (address_2)))) (PreH11 : (0 <= k)) (PreH12 : (k < 72)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app (address_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  EX (address: (@list Z)) ,
  “ (Spec plain address ) ”
  &&  (CharArray.full s_pre ((Zlength (plain)) + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (address)) + 1 ) (app (address) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (address)) + 1 ) 72 )
) \/
(
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (address_2: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((p + 1 ) <= ru)) (PreH8 : ((ru + 1 ) < n)) (PreH9 : (Spec plain address_2 )) (PreH10 : (k = (Zlength (address_2)))) (PreH11 : (0 <= k)) (PreH12 : (k < 72)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app (address_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  EX (address: (@list Z)) ,
  “ (Spec plain address ) ”
  &&  (CharArray.full s_pre ((Zlength (plain)) + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (address)) + 1 ) (app (address) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (address)) + 1 ) 72 )
).

Definition solver_partial_solve_wit_1_pure := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (PreH1 : (1 <= (Zlength (plain)))) (PreH2 : ((Zlength (plain)) <= 50)) (PreH3 : (Pre plain )) (PreH4 : (valid_string plain )) (PreH5 : ((string_length (plain)) = (Zlength (plain)))) (PreH6 : ((string_length (plain)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (store_string s_pre plain )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (valid_string plain ) ” 
  &&  “ ((string_length (plain)) < INT_MAX) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (PreH1 : (1 <= (Zlength (plain)))) (PreH2 : ((Zlength (plain)) <= 50)) (PreH3 : (Pre plain )) (PreH4 : (valid_string plain )) (PreH5 : ((string_length (plain)) = (Zlength (plain)))) (PreH6 : ((string_length (plain)) < INT_MAX)) ,
  (store_string s_pre plain )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ (valid_string plain ) ” 
  &&  “ ((string_length (plain)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (plain)) + 1 )) ” 
  &&  “ (1 <= (Zlength (plain))) ” 
  &&  “ ((Zlength (plain)) <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (valid_string plain ) ” 
  &&  “ ((string_length (plain)) = (Zlength (plain))) ” 
  &&  “ ((string_length (plain)) < INT_MAX) ”
  &&  (store_string s_pre plain )
  **  (CharArray.undef_full out_pre 72 )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((i + 1 ) < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= i)) (PreH9 : (i <= marker)) (PreH10 : ((marker + 1 ) < n)) (PreH11 : ((Znth marker plain 0) = 114)) (PreH12 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH13 : (ru = (-1))) (PreH14 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((i + 1 ) < n) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= i) ” 
  &&  “ (i <= marker) ” 
  &&  “ ((marker + 1 ) < n) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ” 
  &&  “ (ru = (-1)) ” 
  &&  “ (k = 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (plain) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((i + 1 ) < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= i)) (PreH9 : (i <= marker)) (PreH10 : ((marker + 1 ) < n)) (PreH11 : ((Znth marker plain 0) = 114)) (PreH12 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH13 : (ru = (-1))) (PreH14 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((i + 1 ) < n) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= i) ” 
  &&  “ (i <= marker) ” 
  &&  “ ((marker + 1 ) < n) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ” 
  &&  “ (ru = (-1)) ” 
  &&  “ (k = 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (plain) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
.

Definition solver_partial_solve_wit_4 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker)) (PreH11 : ((marker + 1 ) < n)) (PreH12 : ((Znth marker plain 0) = 114)) (PreH13 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114) ” 
  &&  “ ((i + 1 ) < n) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= i) ” 
  &&  “ (i <= marker) ” 
  &&  “ ((marker + 1 ) < n) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ” 
  &&  “ (ru = (-1)) ” 
  &&  “ (k = 0) ”
  &&  (((s_pre + ((i + 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre (i + 1 ) 0 (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
.

Definition solver_partial_solve_wit_5 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (ru: Z) (marker: Z) (i: Z) (p: Z) (n: Z) (PreH1 : ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114)) (PreH2 : ((i + 1 ) < n)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= i)) (PreH10 : (i <= marker)) (PreH11 : ((marker + 1 ) < n)) (PreH12 : ((Znth marker plain 0) = 114)) (PreH13 : ((Znth (marker + 1 ) plain 0) = 117)) (PreH14 : (ru = (-1))) (PreH15 : (k = 0)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
|--
  “ ((Znth i (app (plain) ((cons (0) ((@nil Z))))) 0) = 114) ” 
  &&  “ ((i + 1 ) < n) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= i) ” 
  &&  “ (i <= marker) ” 
  &&  “ ((marker + 1 ) < n) ” 
  &&  “ ((Znth marker plain 0) = 114) ” 
  &&  “ ((Znth (marker + 1 ) plain 0) = 117) ” 
  &&  “ (ru = (-1)) ” 
  &&  “ (k = 0) ”
  &&  (((s_pre + ((i + 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (i + 1 ) (app (plain) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre (i + 1 ) 0 (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 72 )
.

Definition solver_partial_solve_wit_6 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < p)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (0 <= i)) (PreH13 : (i <= p)) (PreH14 : (k = i)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (i < p) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= p) ” 
  &&  “ (k = i) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (plain) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
.

Definition solver_partial_solve_wit_7 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < p)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (0 <= i)) (PreH13 : (i <= p)) (PreH14 : (k = i)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i < p) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= p) ” 
  &&  “ (k = i) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
.

Definition solver_partial_solve_wit_8 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < p)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (0 <= i)) (PreH13 : (i <= p)) (PreH14 : (k = i)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (i < p) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= p) ” 
  &&  “ (k = i) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (plain) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
.

Definition solver_partial_solve_wit_9 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < p)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (0 <= i)) (PreH13 : (i <= p)) (PreH14 : (k = i)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i < p) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= p) ” 
  &&  “ (k = i) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
.

Definition solver_partial_solve_wit_10 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= p)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (0 <= i)) (PreH13 : (i <= p)) (PreH14 : (k = i)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= p) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= p) ” 
  &&  “ (k = i) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
.

Definition solver_partial_solve_wit_11 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= p)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (0 <= i)) (PreH13 : (i <= p)) (PreH14 : (k = i)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= p) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= p) ” 
  &&  “ (k = i) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (sublist (0) (i) (plain)) )
.

Definition solver_partial_solve_wit_12 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= p) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= p) ” 
  &&  “ (k = i) ”
  &&  (((out_pre + ((k + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (k + 1 ) (k + 1 ) 72 )
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z))))) )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_13 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= p) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= p) ” 
  &&  “ (k = i) ”
  &&  (((out_pre + ((k + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (k + 1 ) (k + 1 ) 72 )
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z))))) )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_14 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= p) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= p) ” 
  &&  “ (k = i) ”
  &&  (((out_pre + (((k + 1 ) + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre ((k + 1 ) + 1 ) ((k + 1 ) + 1 ) 72 )
  **  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_15 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= p)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (0 <= i)) (PreH14 : (i <= p)) (PreH15 : (k = i)) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= p) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= p) ” 
  &&  “ (k = i) ”
  &&  (((out_pre + (((k + 1 ) + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre ((k + 1 ) + 1 ) ((k + 1 ) + 1 ) 72 )
  **  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((sublist (0) (i) (plain))) ((cons (58) ((@nil Z)))))) ((cons (47) ((@nil Z))))) )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_16 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < ru)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (p <= i)) (PreH13 : (i <= ru)) (PreH14 : (k = (i + 3 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (i < ru) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= i) ” 
  &&  “ (i <= ru) ” 
  &&  “ (k = (i + 3 )) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (plain) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
.

Definition solver_partial_solve_wit_17 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < ru)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (p <= i)) (PreH13 : (i <= ru)) (PreH14 : (k = (i + 3 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i < ru) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= i) ” 
  &&  “ (i <= ru) ” 
  &&  “ (k = (i + 3 )) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
.

Definition solver_partial_solve_wit_18 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < ru)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (p <= i)) (PreH13 : (i <= ru)) (PreH14 : (k = (i + 3 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (i < ru) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= i) ” 
  &&  “ (i <= ru) ” 
  &&  “ (k = (i + 3 )) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (plain) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
.

Definition solver_partial_solve_wit_19 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < ru)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (p <= i)) (PreH13 : (i <= ru)) (PreH14 : (k = (i + 3 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i < ru) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= i) ” 
  &&  “ (i <= ru) ” 
  &&  “ (k = (i + 3 )) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
.

Definition solver_partial_solve_wit_20 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= ru)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (p <= i)) (PreH13 : (i <= ru)) (PreH14 : (k = (i + 3 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= ru) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= i) ” 
  &&  “ (i <= ru) ” 
  &&  “ (k = (i + 3 )) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
.

Definition solver_partial_solve_wit_21 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i >= ru)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (p <= i)) (PreH13 : (i <= ru)) (PreH14 : (k = (i + 3 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= ru) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= i) ” 
  &&  “ (i <= ru) ” 
  &&  “ (k = (i + 3 )) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain)))))) )
.

Definition solver_partial_solve_wit_22 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= ru) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= i) ” 
  &&  “ (i <= ru) ” 
  &&  “ (k = (i + 3 )) ”
  &&  (((out_pre + ((k + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (k + 1 ) (k + 1 ) 72 )
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z))))) )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_23 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (k + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= ru) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= i) ” 
  &&  “ (i <= ru) ” 
  &&  “ (k = (i + 3 )) ”
  &&  (((out_pre + ((k + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (k + 1 ) (k + 1 ) 72 )
  **  (CharArray.seg out_pre 0 (k + 1 ) (app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z))))) )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_24 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 3)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= ru) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= i) ” 
  &&  “ (i <= ru) ” 
  &&  “ (k = (i + 3 )) ”
  &&  (((out_pre + (((k + 1 ) + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre ((k + 1 ) + 1 ) ((k + 1 ) + 1 ) 72 )
  **  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z))))) )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_25 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i >= ru)) (PreH3 : (n = (Zlength (plain)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : (Pre plain )) (PreH7 : (p = 4)) (PreH8 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH9 : ((p + 1 ) <= ru)) (PreH10 : ((ru + 1 ) < n)) (PreH11 : ((Znth ru plain 0) = 114)) (PreH12 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH13 : (p <= i)) (PreH14 : (i <= ru)) (PreH15 : (k = (i + 3 ))) ,
  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((k + 1 ) + 1 ) 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i >= ru) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (p <= i) ” 
  &&  “ (i <= ru) ” 
  &&  “ (k = (i + 3 )) ”
  &&  (((out_pre + (((k + 1 ) + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre ((k + 1 ) + 1 ) ((k + 1 ) + 1 ) 72 )
  **  (CharArray.seg out_pre 0 ((k + 1 ) + 1 ) (app ((app ((app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((sublist (p) (i) (plain))))))) ((cons (46) ((@nil Z)))))) ((cons (114) ((@nil Z))))) )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_26 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ ((ru + 2 ) < n) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (k = (ru + 6 )) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
.

Definition solver_partial_solve_wit_27 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : ((ru + 2 ) < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 1 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : (k = (ru + 6 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ ((ru + 2 ) < n) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ (k = (ru + 6 )) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((cons (46) ((cons (114) ((cons (117) ((@nil Z))))))))))))) )
.

Definition solver_partial_solve_wit_28 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (i < n) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 2 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((ru + 2 ) <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (k = (i + 5 )) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (plain) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
.

Definition solver_partial_solve_wit_29 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 3)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (102) ((cons (116) ((cons (112) ((@nil Z)))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 2 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((ru + 2 ) <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (k = (i + 5 )) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
.

Definition solver_partial_solve_wit_30 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (i < n) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 2 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((ru + 2 ) <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (k = (i + 5 )) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (plain) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
.

Definition solver_partial_solve_wit_31 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (k: Z) (i: Z) (ru: Z) (p: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (Zlength (plain)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : (Pre plain )) (PreH6 : (p = 4)) (PreH7 : ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z))))))))))) (PreH8 : ((p + 1 ) <= ru)) (PreH9 : ((ru + 2 ) < n)) (PreH10 : ((Znth ru plain 0) = 114)) (PreH11 : ((Znth (ru + 1 ) plain 0) = 117)) (PreH12 : ((ru + 2 ) <= i)) (PreH13 : (i <= n)) (PreH14 : (k = (i + 5 ))) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((sublist (0) (p) (plain)) = (cons (104) ((cons (116) ((cons (116) ((cons (112) ((@nil Z)))))))))) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 2 ) < n) ” 
  &&  “ ((Znth ru plain 0) = 114) ” 
  &&  “ ((Znth (ru + 1 ) plain 0) = 117) ” 
  &&  “ ((ru + 2 ) <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (k = (i + 5 )) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k (app ((sublist (0) (p) (plain))) ((app ((cons (58) ((cons (47) ((cons (47) ((@nil Z)))))))) ((app ((sublist (p) (ru) (plain))) ((app ((cons (46) ((cons (114) ((cons (117) ((@nil Z)))))))) ((app ((cons (47) ((@nil Z)))) ((sublist ((ru + 2 )) (i) (plain)))))))))))) )
.

Definition solver_partial_solve_wit_32 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (address: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 3)) (PreH6 : ((p + 1 ) <= ru)) (PreH7 : ((ru + 1 ) < n)) (PreH8 : (Spec plain address )) (PreH9 : (k = (Zlength (address)))) (PreH10 : (0 <= k)) (PreH11 : (k < 72)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k address )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 3) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ (Spec plain address ) ” 
  &&  “ (k = (Zlength (address))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 72) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k address )
.

Definition solver_partial_solve_wit_33 := 
forall (out_pre: Z) (s_pre: Z) (plain: (@list Z)) (address: (@list Z)) (n: Z) (p: Z) (ru: Z) (k: Z) (PreH1 : (n = (Zlength (plain)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50)) (PreH4 : (Pre plain )) (PreH5 : (p = 4)) (PreH6 : ((p + 1 ) <= ru)) (PreH7 : ((ru + 1 ) < n)) (PreH8 : (Spec plain address )) (PreH9 : (k = (Zlength (address)))) (PreH10 : (0 <= k)) (PreH11 : (k < 72)) ,
  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k address )
  **  (CharArray.undef_seg out_pre k 72 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (n = (Zlength (plain))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50) ” 
  &&  “ (Pre plain ) ” 
  &&  “ (p = 4) ” 
  &&  “ ((p + 1 ) <= ru) ” 
  &&  “ ((ru + 1 ) < n) ” 
  &&  “ (Spec plain address ) ” 
  &&  “ (k = (Zlength (address))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 72) ”
  &&  (((out_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre k k 72 )
  **  (CharArray.full s_pre (n + 1 ) (app (plain) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg out_pre 0 k address )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Axiom proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Axiom proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Axiom proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Axiom proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Axiom proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Axiom proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Axiom proof_of_solver_safety_wit_50 : solver_safety_wit_50.
Axiom proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Axiom proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Axiom proof_of_solver_safety_wit_53 : solver_safety_wit_53.
Axiom proof_of_solver_safety_wit_54 : solver_safety_wit_54.
Axiom proof_of_solver_safety_wit_55 : solver_safety_wit_55.
Axiom proof_of_solver_safety_wit_56 : solver_safety_wit_56.
Axiom proof_of_solver_safety_wit_57 : solver_safety_wit_57.
Axiom proof_of_solver_safety_wit_58 : solver_safety_wit_58.
Axiom proof_of_solver_safety_wit_59 : solver_safety_wit_59.
Axiom proof_of_solver_safety_wit_60 : solver_safety_wit_60.
Axiom proof_of_solver_safety_wit_61 : solver_safety_wit_61.
Axiom proof_of_solver_safety_wit_62 : solver_safety_wit_62.
Axiom proof_of_solver_safety_wit_63 : solver_safety_wit_63.
Axiom proof_of_solver_safety_wit_64 : solver_safety_wit_64.
Axiom proof_of_solver_safety_wit_65 : solver_safety_wit_65.
Axiom proof_of_solver_safety_wit_66 : solver_safety_wit_66.
Axiom proof_of_solver_safety_wit_67 : solver_safety_wit_67.
Axiom proof_of_solver_safety_wit_68 : solver_safety_wit_68.
Axiom proof_of_solver_safety_wit_69 : solver_safety_wit_69.
Axiom proof_of_solver_safety_wit_70 : solver_safety_wit_70.
Axiom proof_of_solver_safety_wit_71 : solver_safety_wit_71.
Axiom proof_of_solver_safety_wit_72 : solver_safety_wit_72.
Axiom proof_of_solver_safety_wit_73 : solver_safety_wit_73.
Axiom proof_of_solver_safety_wit_74 : solver_safety_wit_74.
Axiom proof_of_solver_safety_wit_75 : solver_safety_wit_75.
Axiom proof_of_solver_safety_wit_76 : solver_safety_wit_76.
Axiom proof_of_solver_safety_wit_77 : solver_safety_wit_77.
Axiom proof_of_solver_safety_wit_78 : solver_safety_wit_78.
Axiom proof_of_solver_safety_wit_79 : solver_safety_wit_79.
Axiom proof_of_solver_safety_wit_80 : solver_safety_wit_80.
Axiom proof_of_solver_safety_wit_81 : solver_safety_wit_81.
Axiom proof_of_solver_safety_wit_82 : solver_safety_wit_82.
Axiom proof_of_solver_safety_wit_83 : solver_safety_wit_83.
Axiom proof_of_solver_safety_wit_84 : solver_safety_wit_84.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Axiom proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Axiom proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Axiom proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Axiom proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Axiom proof_of_solver_entail_wit_13_3 : solver_entail_wit_13_3.
Axiom proof_of_solver_entail_wit_13_4 : solver_entail_wit_13_4.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.
Axiom proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29.
Axiom proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30.
Axiom proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31.
Axiom proof_of_solver_partial_solve_wit_32 : solver_partial_solve_wit_32.
Axiom proof_of_solver_partial_solve_wit_33 : solver_partial_solve_wit_33.

End VC_Correct.
