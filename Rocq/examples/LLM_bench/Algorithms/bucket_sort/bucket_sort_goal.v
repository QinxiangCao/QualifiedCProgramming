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
Require Import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib.
Local Open Scope sac.

(*----- Function sort -----*)

Definition sort_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) input )) (PreH4 : (Forall (Z.ge (999999999)) input )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  ((( &( "max_value" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "max_value" ) )) # Int  |-> (Znth 0 input 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall (Z.le (0)) input )) (PreH10 : (Forall (Z.ge (999999999)) input )) (PreH11 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max_value" ) )) # Int  |-> (Znth i input 0))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall (Z.le (0)) input )) (PreH10 : (Forall (Z.ge (999999999)) input )) (PreH11 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall (Z.le (0)) input )) (PreH9 : (Forall (Z.ge (999999999)) input )) (PreH10 : (PrefixMaximum input i max_value )) ,
  ((( &( "exponent" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  (IntArray.full a_pre n_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 1000000000)) (PreH7 : (Forall (Z.le (0)) current )) (PreH8 : (Forall (Z.ge (999999999)) current )) (PreH9 : (PrefixMaximum input n_pre max_value )) (PreH10 : (DecimalExponent exponent )) (PreH11 : (RadixPassState input current exponent )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  “ ((max_value <> (INT_MIN)) \/ (exponent <> (-1))) ” 
  &&  “ (exponent <> 0) ”
.

Definition sort_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 1000000000)) (PreH7 : (Forall (Z.le (0)) current )) (PreH8 : (Forall (Z.ge (999999999)) current )) (PreH9 : (PrefixMaximum input n_pre max_value )) (PreH10 : (DecimalExponent exponent )) (PreH11 : (RadixPassState input current exponent )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall (Z.le (0)) current )) (PreH9 : (Forall (Z.ge (999999999)) current )) (PreH10 : (PrefixMaximum input n_pre max_value )) (PreH11 : (DecimalExponent exponent )) (PreH12 : (RadixPassState input current exponent )) ,
  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (zero_prefix: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= digit)) (PreH9 : (digit <= 10)) (PreH10 : (Forall (Z.le (0)) current )) (PreH11 : (Forall (Z.ge (999999999)) current )) (PreH12 : (Forall (eq (0)) zero_prefix )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current exponent )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) digit 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition sort_safety_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (zero_prefix: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (eq (0)) zero_prefix )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) digit 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_12 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (zero_prefix: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (eq (0)) zero_prefix )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) ,
  (IntArray.seg ( &( "count" ) ) 0 (digit + 1 ) (app (zero_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "count" ) ) (digit + 1 ) 10 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((digit + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit + 1 )) ”
.

Definition sort_safety_wit_13 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (zero_prefix: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (eq (0)) zero_prefix )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) digit 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_14 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (counts: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) counts )) (PreH14 : (Forall (Z.ge (i)) counts )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((((Znth i current 0) ÷ exponent ) <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition sort_safety_wit_15 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (counts: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) counts )) (PreH14 : (Forall (Z.ge (i)) counts )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth i current 0) <> (INT_MIN)) \/ (exponent <> (-1))) ” 
  &&  “ (exponent <> 0) ”
.

Definition sort_safety_wit_16 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (counts: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) counts )) (PreH14 : (Forall (Z.ge (i)) counts )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition sort_safety_wit_17 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (counts: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current )) (PreH11 : (Forall (Z.ge (999999999)) current )) (PreH12 : (Forall (Z.le (0)) counts )) (PreH13 : (Forall (Z.ge (i)) counts )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) (PreH17 : (DigitHistogramPrefix current exponent i counts )) (PreH18 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (IntArray.full ( &( "count" ) ) 10 counts )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth digit counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth digit counts 0) + 1 )) ”
) \/
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (counts: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current )) (PreH11 : (Forall (Z.ge (999999999)) current )) (PreH12 : (Forall (Z.le (0)) counts )) (PreH13 : (Forall (Z.ge (i)) counts )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) (PreH17 : (DigitHistogramPrefix current exponent i counts )) (PreH18 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (IntArray.full ( &( "count" ) ) 10 counts )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth digit counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth digit counts 0) + 1 )) ”
).

Definition sort_safety_wit_17_split_goal_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (counts: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current )) (PreH11 : (Forall (Z.ge (999999999)) current )) (PreH12 : (Forall (Z.le (0)) counts )) (PreH13 : (Forall (Z.ge (i)) counts )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) (PreH17 : (DigitHistogramPrefix current exponent i counts )) (PreH18 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (IntArray.full ( &( "count" ) ) 10 counts )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth digit counts 0) + 1 ) <= INT_MAX) ”
.

Definition sort_safety_wit_17_split_goal_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (counts: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current )) (PreH11 : (Forall (Z.ge (999999999)) current )) (PreH12 : (Forall (Z.le (0)) counts )) (PreH13 : (Forall (Z.ge (i)) counts )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) (PreH17 : (DigitHistogramPrefix current exponent i counts )) (PreH18 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (IntArray.full ( &( "count" ) ) 10 counts )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((INT_MIN) <= ((Znth digit counts 0) + 1 )) ”
.

Definition sort_safety_wit_18 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (counts: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current )) (PreH11 : (Forall (Z.ge (999999999)) current )) (PreH12 : (Forall (Z.le (0)) counts )) (PreH13 : (Forall (Z.ge (i)) counts )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) (PreH17 : (DigitHistogramPrefix current exponent i counts )) (PreH18 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit counts 0) + 1 )) (counts)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_safety_wit_19 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (counts: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) counts )) (PreH14 : (Forall (Z.ge (i)) counts )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent i counts )) ,
  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_20 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (1 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) histogram )) (PreH14 : (Forall (Z.ge (n_pre)) histogram )) (PreH15 : (Forall (Z.le (0)) totals )) (PreH16 : (Forall (Z.ge (n_pre)) totals )) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH21 : (DigitPrefixTotals histogram totals digit )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition sort_safety_wit_21 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) )) ”
) \/
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) )) ”
).

Definition sort_safety_wit_21_split_goal_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) ) <= INT_MAX) ”
.

Definition sort_safety_wit_21_split_goal_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((INT_MIN) <= ((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) )) ”
.

Definition sort_safety_wit_22 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((digit - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit - 1 )) ”
.

Definition sort_safety_wit_23 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_24 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) )) (totals)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((digit + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit + 1 )) ”
.

Definition sort_safety_wit_25 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition sort_safety_wit_26 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_27 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) histogram )) (PreH14 : (Forall (Z.ge (n_pre)) histogram )) (PreH15 : (Forall (Z.le (0)) counters )) (PreH16 : (Forall (Z.ge (n_pre)) counters )) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH21 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_28 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) counters )) (PreH17 : (Forall (Z.ge (n_pre)) counters )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ ((((Znth i current 0) ÷ exponent ) <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition sort_safety_wit_29 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) counters )) (PreH17 : (Forall (Z.ge (n_pre)) counters )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (((Znth i current 0) <> (INT_MIN)) \/ (exponent <> (-1))) ” 
  &&  “ (exponent <> 0) ”
.

Definition sort_safety_wit_30 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) counters )) (PreH17 : (Forall (Z.ge (n_pre)) counters )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition sort_safety_wit_31 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (histogram: (@list Z)) (counters: (@list Z)) (mixed_output: (@list (@option Z))) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) histogram )) (PreH14 : (Forall (Z.ge (n_pre)) histogram )) (PreH15 : (Forall (Z.le (0)) counters )) (PreH16 : (Forall (Z.ge (n_pre)) counters )) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH21 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) (PreH22 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH23 : (0 <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters) (0)))) (PreH26 : ((Znth (digit) (counters) (0)) <= n_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |-> (Znth (digit) (counters) (0)))
  **  (IntArray.missing_i ( &( "count" ) ) digit 0 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (((Znth (digit) (counters) (0)) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (digit) (counters) (0)) - 1 )) ”
.

Definition sort_safety_wit_32 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (histogram: (@list Z)) (counters: (@list Z)) (mixed_output: (@list (@option Z))) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) histogram )) (PreH14 : (Forall (Z.ge (n_pre)) histogram )) (PreH15 : (Forall (Z.le (0)) counters )) (PreH16 : (Forall (Z.ge (n_pre)) counters )) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH21 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) (PreH22 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH23 : (0 <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters) (0)))) (PreH26 : ((Znth (digit) (counters) (0)) <= n_pre)) ,
  (IntArray.mixed_full ( &( "output" ) ) 1000 (replace_Znth (((Znth (digit) (counters) (0)) - 1 )) ((Some ((Znth i current 0)))) (mixed_output)) )
  **  (IntArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth (digit) (counters) (0)) - 1 )) (counters)) )
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition sort_safety_wit_33 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) counters )) (PreH17 : (Forall (Z.ge (n_pre)) counters )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_34 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current exponent )) (PreH16 : (StableDigitPass current pass_output exponent )) (PreH17 : (RadixCopyPrefix current pass_output working i )) ,
  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - 0 ) pass_output 0)) (working)) )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_safety_wit_35 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current exponent )) (PreH16 : (StableDigitPass current pass_output exponent )) (PreH17 : (RadixCopyPrefix current pass_output working i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ ((exponent * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (exponent * 10 )) ”
.

Definition sort_safety_wit_36 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current exponent )) (PreH16 : (StableDigitPass current pass_output exponent )) (PreH17 : (RadixCopyPrefix current pass_output working i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition sort_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= (Znth 0 input 0)) ” 
  &&  “ ((Znth 0 input 0) <= 999999999) ” 
  &&  “ (Forall (Z.le (0)) input ) ” 
  &&  “ (Forall (Z.ge (999999999)) input ) ” 
  &&  “ (PrefixMaximum input 1 (Znth 0 input 0) ) ”
  &&  (IntArray.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  TT && emp 
|--
  “ (PrefixMaximum input 1 (Znth 0 input 0) ) ” 
  &&  “ ((Znth 0 input 0) <= 999999999) ” 
  &&  “ (0 <= (Znth 0 input 0)) ”
  &&  emp
).

Definition sort_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  (PrefixMaximum input 1 (Znth 0 input 0) )
.

Definition sort_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  ((Znth 0 input 0) <= 999999999)
.

Definition sort_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  (0 <= (Znth 0 input 0))
.

Definition sort_entail_wit_2_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall (Z.le (0)) input )) (PreH10 : (Forall (Z.ge (999999999)) input )) (PreH11 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (Znth i input 0)) ” 
  &&  “ ((Znth i input 0) <= 999999999) ” 
  &&  “ (Forall (Z.le (0)) input ) ” 
  &&  “ (Forall (Z.ge (999999999)) input ) ” 
  &&  “ (PrefixMaximum input (i + 1 ) (Znth i input 0) ) ”
  &&  (IntArray.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall (Z.le (0)) input )) (PreH10 : (Forall (Z.ge (999999999)) input )) (PreH11 : (PrefixMaximum input i max_value )) ,
  TT && emp 
|--
  “ (PrefixMaximum input (i + 1 ) (Znth i input 0) ) ” 
  &&  “ ((Znth i input 0) <= 999999999) ”
  &&  emp
).

Definition sort_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall (Z.le (0)) input )) (PreH10 : (Forall (Z.ge (999999999)) input )) (PreH11 : (PrefixMaximum input i max_value )) ,
  (PrefixMaximum input (i + 1 ) (Znth i input 0) )
.

Definition sort_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall (Z.le (0)) input )) (PreH10 : (Forall (Z.ge (999999999)) input )) (PreH11 : (PrefixMaximum input i max_value )) ,
  ((Znth i input 0) <= 999999999)
.

Definition sort_entail_wit_2_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall (Z.le (0)) input )) (PreH10 : (Forall (Z.ge (999999999)) input )) (PreH11 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (Forall (Z.le (0)) input ) ” 
  &&  “ (Forall (Z.ge (999999999)) input ) ” 
  &&  “ (PrefixMaximum input (i + 1 ) max_value ) ”
  &&  (IntArray.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall (Z.le (0)) input )) (PreH10 : (Forall (Z.ge (999999999)) input )) (PreH11 : (PrefixMaximum input i max_value )) ,
  TT && emp 
|--
  “ (PrefixMaximum input (i + 1 ) max_value ) ”
  &&  emp
).

Definition sort_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall (Z.le (0)) input )) (PreH10 : (Forall (Z.ge (999999999)) input )) (PreH11 : (PrefixMaximum input i max_value )) ,
  (PrefixMaximum input (i + 1 ) max_value )
.

Definition sort_entail_wit_3 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall (Z.le (0)) input )) (PreH9 : (Forall (Z.ge (999999999)) input )) (PreH10 : (PrefixMaximum input i max_value )) ,
  (IntArray.undef_full ( &( "count" ) ) 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.full a_pre n_pre input )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 1000000000) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent 1 ) ” 
  &&  “ (RadixPassState input current 1 ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall (Z.le (0)) input )) (PreH9 : (Forall (Z.ge (999999999)) input )) (PreH10 : (PrefixMaximum input i max_value )) ,
  TT && emp 
|--
  “ (RadixPassState input input 1 ) ” 
  &&  “ (DecimalExponent 1 ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ”
  &&  emp
).

Definition sort_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall (Z.le (0)) input )) (PreH9 : (Forall (Z.ge (999999999)) input )) (PreH10 : (PrefixMaximum input i max_value )) ,
  (RadixPassState input input 1 )
.

Definition sort_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall (Z.le (0)) input )) (PreH9 : (Forall (Z.ge (999999999)) input )) (PreH10 : (PrefixMaximum input i max_value )) ,
  (DecimalExponent 1 )
.

Definition sort_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall (Z.le (0)) input )) (PreH9 : (Forall (Z.ge (999999999)) input )) (PreH10 : (PrefixMaximum input i max_value )) ,
  (PrefixMaximum input n_pre max_value )
.

Definition sort_entail_wit_4 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall (Z.le (0)) current_2 )) (PreH9 : (Forall (Z.ge (999999999)) current_2 )) (PreH10 : (PrefixMaximum input n_pre max_value )) (PreH11 : (DecimalExponent exponent )) (PreH12 : (RadixPassState input current_2 exponent )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  EX (zero_prefix: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (eq (0)) zero_prefix ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 0 zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) 0 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall (Z.le (0)) current_2 )) (PreH9 : (Forall (Z.ge (999999999)) current_2 )) (PreH10 : (PrefixMaximum input n_pre max_value )) (PreH11 : (DecimalExponent exponent )) (PreH12 : (RadixPassState input current_2 exponent )) ,
  TT && emp 
|--
  “ (Forall (eq (0)) (@nil Z) ) ” 
  &&  “ (exponent <= 100000000) ”
  &&  emp
).

Definition sort_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall (Z.le (0)) current_2 )) (PreH9 : (Forall (Z.ge (999999999)) current_2 )) (PreH10 : (PrefixMaximum input n_pre max_value )) (PreH11 : (DecimalExponent exponent )) (PreH12 : (RadixPassState input current_2 exponent )) ,
  (Forall (eq (0)) (@nil Z) )
.

Definition sort_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall (Z.le (0)) current_2 )) (PreH9 : (Forall (Z.ge (999999999)) current_2 )) (PreH10 : (PrefixMaximum input n_pre max_value )) (PreH11 : (DecimalExponent exponent )) (PreH12 : (RadixPassState input current_2 exponent )) ,
  (exponent <= 100000000)
.

Definition sort_entail_wit_5 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (zero_prefix_2: (@list Z)) (current_2: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall (Z.le (0)) current_2 )) (PreH12 : (Forall (Z.ge (999999999)) current_2 )) (PreH13 : (Forall (eq (0)) zero_prefix_2 )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) ,
  (IntArray.seg ( &( "count" ) ) 0 (digit + 1 ) (app (zero_prefix_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "count" ) ) (digit + 1 ) 10 )
  **  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (zero_prefix: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= (digit + 1 )) ” 
  &&  “ ((digit + 1 ) <= 10) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (eq (0)) zero_prefix ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 (digit + 1 ) zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) (digit + 1 ) 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (zero_prefix_2: (@list Z)) (current_2: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall (Z.le (0)) current_2 )) (PreH12 : (Forall (Z.ge (999999999)) current_2 )) (PreH13 : (Forall (eq (0)) zero_prefix_2 )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) ,
  TT && emp 
|--
  “ (Forall (eq (0)) (app (zero_prefix_2) ((cons (0) ((@nil Z))))) ) ”
  &&  emp
).

Definition sort_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (zero_prefix_2: (@list Z)) (current_2: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall (Z.le (0)) current_2 )) (PreH12 : (Forall (Z.ge (999999999)) current_2 )) (PreH13 : (Forall (eq (0)) zero_prefix_2 )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) ,
  (Forall (eq (0)) (app (zero_prefix_2) ((cons (0) ((@nil Z))))) )
.

Definition sort_entail_wit_6 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (zero_prefix: (@list Z)) (current_2: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall (Z.le (0)) current_2 )) (PreH12 : (Forall (Z.ge (999999999)) current_2 )) (PreH13 : (Forall (eq (0)) zero_prefix )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) digit 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (counts: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (0)) counts ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent 0 counts ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (zero_prefix: (@list Z)) (current_2: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall (Z.le (0)) current_2 )) (PreH12 : (Forall (Z.ge (999999999)) current_2 )) (PreH13 : (Forall (eq (0)) zero_prefix )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) ,
  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
|--
  EX (counts: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_2 ) ” 
  &&  “ (Forall (Z.ge (999999999)) current_2 ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (0)) counts ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current_2 exponent ) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent 0 counts ) ”
  &&  (IntArray.full ( &( "count" ) ) 10 counts )
).

Definition sort_entail_wit_7 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (counts_2: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) counts_2 )) (PreH14 : (Forall (Z.ge (i)) counts_2 )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent i counts_2 )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (counts: (@list Z))  (current_2: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_2 ) ” 
  &&  “ (Forall (Z.ge (999999999)) current_2 ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current_2 exponent ) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent i counts ) ” 
  &&  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) = (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10) ”
  &&  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (counts_2: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) counts_2 )) (PreH14 : (Forall (Z.ge (i)) counts_2 )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent i counts_2 )) ,
  TT && emp 
|--
  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) )) ”
  &&  emp
).

Definition sort_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (counts_2: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) counts_2 )) (PreH14 : (Forall (Z.ge (i)) counts_2 )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent i counts_2 )) ,
  ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10)
.

Definition sort_entail_wit_7_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (counts_2: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) counts_2 )) (PreH14 : (Forall (Z.ge (i)) counts_2 )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent i counts_2 )) ,
  (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) ))
.

Definition sort_entail_wit_8 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (counts_2: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current_2 )) (PreH11 : (Forall (Z.ge (999999999)) current_2 )) (PreH12 : (Forall (Z.le (0)) counts_2 )) (PreH13 : (Forall (Z.ge (i)) counts_2 )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent i counts_2 )) (PreH18 : (digit = (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (counts: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) counts ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent (i + 1 ) counts ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (counts_2: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current_2 )) (PreH11 : (Forall (Z.ge (999999999)) current_2 )) (PreH12 : (Forall (Z.le (0)) counts_2 )) (PreH13 : (Forall (Z.ge (i)) counts_2 )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent i counts_2 )) (PreH18 : (digit = (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  TT && emp 
|--
  “ (DigitHistogramPrefix current_2 exponent (i + 1 ) (replace_Znth (digit) (((Znth digit counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) (replace_Znth (digit) (((Znth digit counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (digit) (((Znth digit counts_2 0) + 1 )) (counts_2)) ) ”
  &&  emp
).

Definition sort_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (counts_2: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current_2 )) (PreH11 : (Forall (Z.ge (999999999)) current_2 )) (PreH12 : (Forall (Z.le (0)) counts_2 )) (PreH13 : (Forall (Z.ge (i)) counts_2 )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent i counts_2 )) (PreH18 : (digit = (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (DigitHistogramPrefix current_2 exponent (i + 1 ) (replace_Znth (digit) (((Znth digit counts_2 0) + 1 )) (counts_2)) )
.

Definition sort_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (counts_2: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current_2 )) (PreH11 : (Forall (Z.ge (999999999)) current_2 )) (PreH12 : (Forall (Z.le (0)) counts_2 )) (PreH13 : (Forall (Z.ge (i)) counts_2 )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent i counts_2 )) (PreH18 : (digit = (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (Forall (Z.ge ((i + 1 ))) (replace_Znth (digit) (((Znth digit counts_2 0) + 1 )) (counts_2)) )
.

Definition sort_entail_wit_8_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (counts_2: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current_2 )) (PreH11 : (Forall (Z.ge (999999999)) current_2 )) (PreH12 : (Forall (Z.le (0)) counts_2 )) (PreH13 : (Forall (Z.ge (i)) counts_2 )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent i counts_2 )) (PreH18 : (digit = (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (Forall (Z.le (0)) (replace_Znth (digit) (((Znth digit counts_2 0) + 1 )) (counts_2)) )
.

Definition sort_entail_wit_9 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (counts: (@list Z)) (current_2: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current_2 )) (PreH12 : (Forall (Z.ge (999999999)) current_2 )) (PreH13 : (Forall (Z.le (0)) counts )) (PreH14 : (Forall (Z.ge (i)) counts )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current_2 exponent )) (PreH18 : (DigitHistogramPrefix current_2 exponent i counts )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (totals: (@list Z))  (current: (@list Z))  (histogram: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 10) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) totals ) ” 
  &&  “ (Forall (Z.ge (n_pre)) totals ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals 1 ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (counts: (@list Z)) (current_2: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current_2 )) (PreH12 : (Forall (Z.ge (999999999)) current_2 )) (PreH13 : (Forall (Z.le (0)) counts )) (PreH14 : (Forall (Z.ge (i)) counts )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current_2 exponent )) (PreH18 : (DigitHistogramPrefix current_2 exponent i counts )) ,
  TT && emp 
|--
  EX (histogram: (@list Z)) ,
  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 10) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) counts ) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram counts 1 ) ”
  &&  emp
).

Definition sort_entail_wit_10 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals_2: (@list Z)) (current_2: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram_2: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current_2 )) (PreH13 : (Forall (Z.ge (999999999)) current_2 )) (PreH14 : (Forall (Z.le (0)) histogram_2 )) (PreH15 : (Forall (Z.ge (n_pre)) histogram_2 )) (PreH16 : (Forall (Z.le (0)) totals_2 )) (PreH17 : (Forall (Z.ge (n_pre)) totals_2 )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current_2 exponent )) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH22 : (DigitPrefixTotals histogram_2 totals_2 digit )) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit totals_2 0) + (Znth (digit - 1 ) totals_2 0) )) (totals_2)) )
  **  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (totals: (@list Z))  (current: (@list Z))  (histogram: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (1 <= (digit + 1 )) ” 
  &&  “ ((digit + 1 ) <= 10) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) totals ) ” 
  &&  “ (Forall (Z.ge (n_pre)) totals ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals (digit + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (totals_2: (@list Z)) (current_2: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram_2: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current_2 )) (PreH13 : (Forall (Z.ge (999999999)) current_2 )) (PreH14 : (Forall (Z.le (0)) histogram_2 )) (PreH15 : (Forall (Z.ge (n_pre)) histogram_2 )) (PreH16 : (Forall (Z.le (0)) totals_2 )) (PreH17 : (Forall (Z.ge (n_pre)) totals_2 )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current_2 exponent )) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH22 : (DigitPrefixTotals histogram_2 totals_2 digit )) ,
  TT && emp 
|--
  EX (histogram: (@list Z)) ,
  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (1 <= (digit + 1 )) ” 
  &&  “ ((digit + 1 ) <= 10) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (digit) (((Znth digit totals_2 0) + (Znth (digit - 1 ) totals_2 0) )) (totals_2)) ) ” 
  &&  “ (Forall (Z.ge (n_pre)) (replace_Znth (digit) (((Znth digit totals_2 0) + (Znth (digit - 1 ) totals_2 0) )) (totals_2)) ) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram (replace_Znth (digit) (((Znth digit totals_2 0) + (Znth (digit - 1 ) totals_2 0) )) (totals_2)) (digit + 1 ) ) ”
  &&  emp
).

Definition sort_entail_wit_11 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current_2: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram_2: (@list Z)) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current_2 )) (PreH13 : (Forall (Z.ge (999999999)) current_2 )) (PreH14 : (Forall (Z.le (0)) histogram_2 )) (PreH15 : (Forall (Z.ge (n_pre)) histogram_2 )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current_2 exponent )) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH22 : (DigitPrefixTotals histogram_2 totals digit )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (mixed_output: (@list (@option Z)))  (counters: (@list Z))  (current: (@list Z))  (histogram: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) counters ) ” 
  &&  “ (Forall (Z.ge (n_pre)) counters ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent ((n_pre - 1 ) + 1 ) histogram counters mixed_output ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current_2: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram_2: (@list Z)) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current_2 )) (PreH13 : (Forall (Z.ge (999999999)) current_2 )) (PreH14 : (Forall (Z.le (0)) histogram_2 )) (PreH15 : (Forall (Z.ge (n_pre)) histogram_2 )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current_2 exponent )) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH22 : (DigitPrefixTotals histogram_2 totals digit )) ,
  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (mixed_output: (@list (@option Z)))  (histogram: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_2 ) ” 
  &&  “ (Forall (Z.ge (999999999)) current_2 ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) totals ) ” 
  &&  “ (Forall (Z.ge (n_pre)) totals ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current_2 exponent ) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current_2 exponent ((n_pre - 1 ) + 1 ) histogram totals mixed_output ) ”
  &&  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
).

Definition sort_entail_wit_12 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (mixed_output_2: (@list (@option Z))) (counters_2: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (histogram_2: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram_2 )) (PreH15 : (Forall (Z.ge (n_pre)) histogram_2 )) (PreH16 : (Forall (Z.le (0)) counters_2 )) (PreH17 : (Forall (Z.ge (n_pre)) counters_2 )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram_2 )) (PreH22 : (BucketPlacementProgress current exponent (i + 1 ) histogram_2 counters_2 mixed_output_2 )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters_2 )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output_2 )
|--
  EX (mixed_output: (@list (@option Z)))  (counters: (@list Z))  (current_2: (@list Z))  (histogram: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_2 ) ” 
  &&  “ (Forall (Z.ge (999999999)) current_2 ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) counters ) ” 
  &&  “ (Forall (Z.ge (n_pre)) counters ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current_2 exponent ) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current_2 exponent (i + 1 ) histogram counters mixed_output ) ” 
  &&  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) = (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (1 <= (Znth ((((Znth i current 0) ÷ exponent ) % ( 10 ) )) (counters) (0))) ” 
  &&  “ ((Znth ((((Znth i current 0) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre) ”
  &&  (IntArray.full a_pre n_pre current_2 )
  **  (((( &( "count" ) ) + ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((Znth i current 0) ÷ exponent ) % ( 10 ) )) (counters) (0)))
  **  (IntArray.missing_i ( &( "count" ) ) (((Znth i current 0) ÷ exponent ) % ( 10 ) ) 0 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (mixed_output_2: (@list (@option Z))) (counters_2: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (histogram_2: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram_2 )) (PreH15 : (Forall (Z.ge (n_pre)) histogram_2 )) (PreH16 : (Forall (Z.le (0)) counters_2 )) (PreH17 : (Forall (Z.ge (n_pre)) counters_2 )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram_2 )) (PreH22 : (BucketPlacementProgress current exponent (i + 1 ) histogram_2 counters_2 mixed_output_2 )) ,
  (IntArray.full ( &( "count" ) ) 10 counters_2 )
|--
  EX (counters: (@list Z))  (histogram: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) counters ) ” 
  &&  “ (Forall (Z.ge (n_pre)) counters ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output_2 ) ” 
  &&  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (1 <= (Znth ((((Znth i current 0) ÷ exponent ) % ( 10 ) )) (counters) (0))) ” 
  &&  “ ((Znth ((((Znth i current 0) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre) ”
  &&  (((( &( "count" ) ) + ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((Znth i current 0) ÷ exponent ) % ( 10 ) )) (counters) (0)))
  **  (IntArray.missing_i ( &( "count" ) ) (((Znth i current 0) ÷ exponent ) % ( 10 ) ) 0 10 counters )
).

Definition sort_entail_wit_13 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (histogram_2: (@list Z)) (counters_2: (@list Z)) (mixed_output_2: (@list (@option Z))) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram_2)) = 10)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall (Z.le (0)) current_2 )) (PreH12 : (Forall (Z.ge (999999999)) current_2 )) (PreH13 : (Forall (Z.le (0)) histogram_2 )) (PreH14 : (Forall (Z.ge (n_pre)) histogram_2 )) (PreH15 : (Forall (Z.le (0)) counters_2 )) (PreH16 : (Forall (Z.ge (n_pre)) counters_2 )) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) (PreH20 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH21 : (BucketPlacementProgress current_2 exponent (i + 1 ) histogram_2 counters_2 mixed_output_2 )) (PreH22 : (digit = (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) (PreH23 : (0 <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters_2) (0)))) (PreH26 : ((Znth (digit) (counters_2) (0)) <= n_pre)) ,
  (IntArray.mixed_full ( &( "output" ) ) 1000 (replace_Znth (((Znth (digit) (counters_2) (0)) - 1 )) ((Some ((Znth i current_2 0)))) (mixed_output_2)) )
  **  (IntArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth (digit) (counters_2) (0)) - 1 )) (counters_2)) )
  **  (IntArray.full a_pre n_pre current_2 )
|--
  EX (mixed_output: (@list (@option Z)))  (counters: (@list Z))  (current: (@list Z))  (histogram: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) counters ) ” 
  &&  “ (Forall (Z.ge (n_pre)) counters ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent ((i - 1 ) + 1 ) histogram counters mixed_output ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (histogram_2: (@list Z)) (counters_2: (@list Z)) (mixed_output_2: (@list (@option Z))) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram_2)) = 10)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall (Z.le (0)) current_2 )) (PreH12 : (Forall (Z.ge (999999999)) current_2 )) (PreH13 : (Forall (Z.le (0)) histogram_2 )) (PreH14 : (Forall (Z.ge (n_pre)) histogram_2 )) (PreH15 : (Forall (Z.le (0)) counters_2 )) (PreH16 : (Forall (Z.ge (n_pre)) counters_2 )) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) (PreH20 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH21 : (BucketPlacementProgress current_2 exponent (i + 1 ) histogram_2 counters_2 mixed_output_2 )) (PreH22 : (digit = (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) (PreH23 : (0 <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters_2) (0)))) (PreH26 : ((Znth (digit) (counters_2) (0)) <= n_pre)) ,
  TT && emp 
|--
  EX (histogram: (@list Z)) ,
  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) - 1 )) (counters_2)) ) ” 
  &&  “ (Forall (Z.ge (n_pre)) (replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) - 1 )) (counters_2)) ) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current_2 exponent ((i - 1 ) + 1 ) histogram (replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) - 1 )) (counters_2)) (replace_Znth (((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) - 1 )) ((Some ((Znth i current_2 0)))) (mixed_output_2)) ) ”
  &&  emp
).

Definition sort_entail_wit_14 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (current_2: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall (Z.le (0)) current_2 )) (PreH13 : (Forall (Z.ge (999999999)) current_2 )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) counters )) (PreH17 : (Forall (Z.ge (n_pre)) counters )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current_2 exponent )) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram )) (PreH22 : (BucketPlacementProgress current_2 exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  EX (bucket_starts: (@list Z))  (working: (@list Z))  (pass_output: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (Forall (Z.le (0)) pass_output ) ” 
  &&  “ (Forall (Z.ge (999999999)) pass_output ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output working 0 ) ”
  &&  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (current_2: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall (Z.le (0)) current_2 )) (PreH13 : (Forall (Z.ge (999999999)) current_2 )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) counters )) (PreH17 : (Forall (Z.ge (n_pre)) counters )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current_2 exponent )) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram )) (PreH22 : (BucketPlacementProgress current_2 exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  EX (pass_output: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (Forall (Z.le (0)) pass_output ) ” 
  &&  “ (Forall (Z.ge (999999999)) pass_output ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output current_2 0 ) ”
  &&  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
).

Definition sort_entail_wit_15 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (bucket_starts_2: (@list Z)) (working_2: (@list Z)) (pass_output_2: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output_2 )) (PreH12 : (Forall (Z.ge (999999999)) pass_output_2 )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current_2 exponent )) (PreH16 : (StableDigitPass current_2 pass_output_2 exponent )) (PreH17 : (RadixCopyPrefix current_2 pass_output_2 working_2 i )) ,
  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - 0 ) pass_output_2 0)) (working_2)) )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output_2 )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  EX (bucket_starts: (@list Z))  (working: (@list Z))  (pass_output: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (Forall (Z.le (0)) pass_output ) ” 
  &&  “ (Forall (Z.ge (999999999)) pass_output ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output working (i + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (working_2: (@list Z)) (pass_output_2: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output_2 )) (PreH12 : (Forall (Z.ge (999999999)) pass_output_2 )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current_2 exponent )) (PreH16 : (StableDigitPass current_2 pass_output_2 exponent )) (PreH17 : (RadixCopyPrefix current_2 pass_output_2 working_2 i )) ,
  TT && emp 
|--
  EX (current: (@list Z)) ,
  “ ((Zlength (current)) = (Zlength (current_2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (current_2))) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output_2 exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output_2 (replace_Znth (i) ((Znth (i - 0 ) pass_output_2 0)) (working_2)) (i + 1 ) ) ”
  &&  emp
).

Definition sort_entail_wit_16 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current_2 exponent )) (PreH16 : (StableDigitPass current_2 pass_output exponent )) (PreH17 : (RadixCopyPrefix current_2 pass_output working i )) ,
  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= (exponent * 10 )) ” 
  &&  “ ((exponent * 10 ) <= 1000000000) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent (exponent * 10 ) ) ” 
  &&  “ (RadixPassState input current (exponent * 10 ) ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current_2 exponent )) (PreH16 : (StableDigitPass current_2 pass_output exponent )) (PreH17 : (RadixCopyPrefix current_2 pass_output working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (RadixPassState input working (exponent * 10 ) ) ” 
  &&  “ (DecimalExponent (exponent * 10 ) ) ” 
  &&  “ (Forall (Z.ge (999999999)) working ) ” 
  &&  “ (Forall (Z.le (0)) working ) ”
  &&  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
).

Definition sort_entail_wit_16_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current_2 exponent )) (PreH16 : (StableDigitPass current_2 pass_output exponent )) (PreH17 : (RadixCopyPrefix current_2 pass_output working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (RadixPassState input working (exponent * 10 ) ) ”
.

Definition sort_entail_wit_16_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current_2 exponent )) (PreH16 : (StableDigitPass current_2 pass_output exponent )) (PreH17 : (RadixCopyPrefix current_2 pass_output working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (DecimalExponent (exponent * 10 ) ) ”
.

Definition sort_entail_wit_16_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current_2 exponent )) (PreH16 : (StableDigitPass current_2 pass_output exponent )) (PreH17 : (RadixCopyPrefix current_2 pass_output working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (Forall (Z.ge (999999999)) working ) ”
.

Definition sort_entail_wit_16_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current_2 exponent )) (PreH16 : (StableDigitPass current_2 pass_output exponent )) (PreH17 : (RadixCopyPrefix current_2 pass_output working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (Forall (Z.le (0)) working ) ”
.

Definition sort_entail_wit_16_split_goal_spatial := 
forall (n_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current_2 exponent )) (PreH16 : (StableDigitPass current_2 pass_output exponent )) (PreH17 : (RadixCopyPrefix current_2 pass_output working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
.

Definition sort_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre <= 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  (IntArray.full a_pre n_pre input )
|--
  EX (output: (@list Z)) ,
  “ (Permutation input output ) ” 
  &&  “ (increasing output ) ”
  &&  (IntArray.full a_pre n_pre output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre <= 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  TT && emp 
|--
  “ (increasing input ) ” 
  &&  “ (Permutation input input ) ”
  &&  emp
).

Definition sort_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre <= 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  (increasing input )
.

Definition sort_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre <= 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  (Permutation input input )
.

Definition sort_return_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : ((max_value ÷ exponent ) <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall (Z.le (0)) current )) (PreH9 : (Forall (Z.ge (999999999)) current )) (PreH10 : (PrefixMaximum input n_pre max_value )) (PreH11 : (DecimalExponent exponent )) (PreH12 : (RadixPassState input current exponent )) ,
  (IntArray.full a_pre n_pre current )
|--
  EX (output: (@list Z)) ,
  “ (Permutation input output ) ” 
  &&  “ (increasing output ) ”
  &&  (IntArray.full a_pre n_pre output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (current: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : ((max_value ÷ exponent ) <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall (Z.le (0)) current )) (PreH9 : (Forall (Z.ge (999999999)) current )) (PreH10 : (PrefixMaximum input n_pre max_value )) (PreH11 : (DecimalExponent exponent )) (PreH12 : (RadixPassState input current exponent )) ,
  TT && emp 
|--
  “ (increasing current ) ” 
  &&  “ (Permutation input current ) ”
  &&  emp
).

Definition sort_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (current: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : ((max_value ÷ exponent ) <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall (Z.le (0)) current )) (PreH9 : (Forall (Z.ge (999999999)) current )) (PreH10 : (PrefixMaximum input n_pre max_value )) (PreH11 : (DecimalExponent exponent )) (PreH12 : (RadixPassState input current exponent )) ,
  (increasing current )
.

Definition sort_return_wit_2_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (current: (@list Z)) (exponent: Z) (max_value: Z) (PreH1 : ((max_value ÷ exponent ) <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall (Z.le (0)) current )) (PreH9 : (Forall (Z.ge (999999999)) current )) (PreH10 : (PrefixMaximum input n_pre max_value )) (PreH11 : (DecimalExponent exponent )) (PreH12 : (RadixPassState input current exponent )) ,
  (Permutation input current )
.

Definition sort_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) input )) (PreH5 : (Forall (Z.ge (999999999)) input )) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (n_pre > 1) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) input ) ” 
  &&  “ (Forall (Z.ge (999999999)) input ) ”
  &&  (((a_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 input 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre input )
.

Definition sort_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall (Z.le (0)) input )) (PreH9 : (Forall (Z.ge (999999999)) input )) (PreH10 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (Forall (Z.le (0)) input ) ” 
  &&  “ (Forall (Z.ge (999999999)) input ) ” 
  &&  “ (PrefixMaximum input i max_value ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
.

Definition sort_partial_solve_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall (Z.le (0)) input )) (PreH10 : (Forall (Z.ge (999999999)) input )) (PreH11 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
|--
  “ ((Znth i input 0) > max_value) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (Forall (Z.le (0)) input ) ” 
  &&  “ (Forall (Z.ge (999999999)) input ) ” 
  &&  “ (PrefixMaximum input i max_value ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
.

Definition sort_partial_solve_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (zero_prefix: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (eq (0)) zero_prefix )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) digit 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (digit < 10) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= digit) ” 
  &&  “ (digit <= 10) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (eq (0)) zero_prefix ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "count" ) ) (digit + 1 ) 10 )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (counts: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) counts )) (PreH14 : (Forall (Z.ge (i)) counts )) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent i counts ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i current 0))
  **  (IntArray.missing_i a_pre i 0 n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (counts: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current )) (PreH11 : (Forall (Z.ge (999999999)) current )) (PreH12 : (Forall (Z.le (0)) counts )) (PreH13 : (Forall (Z.ge (i)) counts )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) (PreH17 : (DigitHistogramPrefix current exponent i counts )) (PreH18 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent i counts ) ” 
  &&  “ (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ (0 <= digit) ” 
  &&  “ (digit < 10) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |-> (Znth digit counts 0))
  **  (IntArray.missing_i ( &( "count" ) ) digit 0 10 counts )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (counts: (@list Z)) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : (0 < (max_value ÷ exponent ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.le (0)) current )) (PreH11 : (Forall (Z.ge (999999999)) current )) (PreH12 : (Forall (Z.le (0)) counts )) (PreH13 : (Forall (Z.ge (i)) counts )) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) (PreH17 : (DigitHistogramPrefix current exponent i counts )) (PreH18 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH19 : (0 <= digit)) (PreH20 : (digit < 10)) ,
  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent i counts ) ” 
  &&  “ (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ (0 <= digit) ” 
  &&  “ (digit < 10) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "count" ) ) digit 0 10 counts )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (digit < 10) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (1 <= digit) ” 
  &&  “ (digit <= 10) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) totals ) ” 
  &&  “ (Forall (Z.ge (n_pre)) totals ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals digit ) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |-> (Znth digit totals 0))
  **  (IntArray.missing_i ( &( "count" ) ) digit 0 10 totals )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (digit < 10) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (1 <= digit) ” 
  &&  “ (digit <= 10) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) totals ) ” 
  &&  “ (Forall (Z.ge (n_pre)) totals ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals digit ) ”
  &&  (((( &( "count" ) ) + ((digit - 1 ) * sizeof(INT)))) # Int  |-> (Znth (digit - 1 ) totals 0))
  **  (IntArray.missing_i ( &( "count" ) ) (digit - 1 ) 0 10 totals )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (totals: (@list Z)) (current: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) totals )) (PreH17 : (Forall (Z.ge (n_pre)) totals )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (digit < 10) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (1 <= digit) ” 
  &&  “ (digit <= 10) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) totals ) ” 
  &&  “ (Forall (Z.ge (n_pre)) totals ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals digit ) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "count" ) ) digit 0 10 totals )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (current: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (histogram: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 < (max_value ÷ exponent ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall (Z.le (0)) current )) (PreH13 : (Forall (Z.ge (999999999)) current )) (PreH14 : (Forall (Z.le (0)) histogram )) (PreH15 : (Forall (Z.ge (n_pre)) histogram )) (PreH16 : (Forall (Z.le (0)) counters )) (PreH17 : (Forall (Z.ge (n_pre)) counters )) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) counters ) ” 
  &&  “ (Forall (Z.ge (n_pre)) counters ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i current 0))
  **  (IntArray.missing_i a_pre i 0 n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
.

Definition sort_partial_solve_wit_12 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (histogram: (@list Z)) (counters: (@list Z)) (mixed_output: (@list (@option Z))) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) histogram )) (PreH14 : (Forall (Z.ge (n_pre)) histogram )) (PreH15 : (Forall (Z.le (0)) counters )) (PreH16 : (Forall (Z.ge (n_pre)) counters )) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH21 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) (PreH22 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH23 : (0 <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters) (0)))) (PreH26 : ((Znth (digit) (counters) (0)) <= n_pre)) ,
  (IntArray.full a_pre n_pre current )
  **  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |-> ((Znth (digit) (counters) (0)) - 1 ))
  **  (IntArray.missing_i ( &( "count" ) ) digit 0 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) counters ) ” 
  &&  “ (Forall (Z.ge (n_pre)) counters ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ” 
  &&  “ (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ (0 <= digit) ” 
  &&  “ (digit < 10) ” 
  &&  “ (1 <= (Znth (digit) (counters) (0))) ” 
  &&  “ ((Znth (digit) (counters) (0)) <= n_pre) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i current 0))
  **  (IntArray.missing_i a_pre i 0 n_pre current )
  **  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |-> ((Znth (digit) (counters) (0)) - 1 ))
  **  (IntArray.missing_i ( &( "count" ) ) digit 0 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
.

Definition sort_partial_solve_wit_13 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (histogram: (@list Z)) (counters: (@list Z)) (mixed_output: (@list (@option Z))) (max_value: Z) (exponent: Z) (i: Z) (digit: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : (0 <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : (0 < (max_value ÷ exponent ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall (Z.le (0)) current )) (PreH12 : (Forall (Z.ge (999999999)) current )) (PreH13 : (Forall (Z.le (0)) histogram )) (PreH14 : (Forall (Z.ge (n_pre)) histogram )) (PreH15 : (Forall (Z.le (0)) counters )) (PreH16 : (Forall (Z.ge (n_pre)) counters )) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH21 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) (PreH22 : (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH23 : (0 <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters) (0)))) (PreH26 : ((Znth (digit) (counters) (0)) <= n_pre)) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth (digit) (counters) (0)) - 1 )) (counters)) )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.le (0)) current ) ” 
  &&  “ (Forall (Z.ge (999999999)) current ) ” 
  &&  “ (Forall (Z.le (0)) histogram ) ” 
  &&  “ (Forall (Z.ge (n_pre)) histogram ) ” 
  &&  “ (Forall (Z.le (0)) counters ) ” 
  &&  “ (Forall (Z.ge (n_pre)) counters ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ” 
  &&  “ (digit = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ (0 <= digit) ” 
  &&  “ (digit < 10) ” 
  &&  “ (1 <= (Znth (digit) (counters) (0))) ” 
  &&  “ ((Znth (digit) (counters) (0)) <= n_pre) ”
  &&  (((( &( "output" ) ) + (((Znth (digit) (counters) (0)) - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i ( &( "output" ) ) ((Znth (digit) (counters) (0)) - 1 ) 0 1000 mixed_output )
  **  (IntArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth (digit) (counters) (0)) - 1 )) (counters)) )
  **  (IntArray.full a_pre n_pre current )
.

Definition sort_partial_solve_wit_14 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current exponent )) (PreH16 : (StableDigitPass current pass_output exponent )) (PreH17 : (RadixCopyPrefix current pass_output working i )) ,
  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (Forall (Z.le (0)) pass_output ) ” 
  &&  “ (Forall (Z.ge (999999999)) pass_output ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output working i ) ”
  &&  (((( &( "output" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) pass_output 0))
  **  (IntArray.missing_i ( &( "output" ) ) i 0 n_pre pass_output )
  **  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
.

Definition sort_partial_solve_wit_15 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (bucket_starts: (@list Z)) (working: (@list Z)) (pass_output: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall (Z.le (0)) pass_output )) (PreH12 : (Forall (Z.ge (999999999)) pass_output )) (PreH13 : (PrefixMaximum input n_pre max_value )) (PreH14 : (DecimalExponent exponent )) (PreH15 : (RadixPassState input current exponent )) (PreH16 : (StableDigitPass current pass_output exponent )) (PreH17 : (RadixCopyPrefix current pass_output working i )) ,
  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (Forall (Z.le (0)) pass_output ) ” 
  &&  “ (Forall (Z.ge (999999999)) pass_output ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output working i ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre i 0 n_pre working )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
.

Module Type VC_Correct.


Axiom proof_of_sort_safety_wit_1 : sort_safety_wit_1.
Axiom proof_of_sort_safety_wit_2 : sort_safety_wit_2.
Axiom proof_of_sort_safety_wit_3 : sort_safety_wit_3.
Axiom proof_of_sort_safety_wit_4 : sort_safety_wit_4.
Axiom proof_of_sort_safety_wit_5 : sort_safety_wit_5.
Axiom proof_of_sort_safety_wit_6 : sort_safety_wit_6.
Axiom proof_of_sort_safety_wit_7 : sort_safety_wit_7.
Axiom proof_of_sort_safety_wit_8 : sort_safety_wit_8.
Axiom proof_of_sort_safety_wit_9 : sort_safety_wit_9.
Axiom proof_of_sort_safety_wit_10 : sort_safety_wit_10.
Axiom proof_of_sort_safety_wit_11 : sort_safety_wit_11.
Axiom proof_of_sort_safety_wit_12 : sort_safety_wit_12.
Axiom proof_of_sort_safety_wit_13 : sort_safety_wit_13.
Axiom proof_of_sort_safety_wit_14 : sort_safety_wit_14.
Axiom proof_of_sort_safety_wit_15 : sort_safety_wit_15.
Axiom proof_of_sort_safety_wit_16 : sort_safety_wit_16.
Axiom proof_of_sort_safety_wit_17 : sort_safety_wit_17.
Axiom proof_of_sort_safety_wit_18 : sort_safety_wit_18.
Axiom proof_of_sort_safety_wit_19 : sort_safety_wit_19.
Axiom proof_of_sort_safety_wit_20 : sort_safety_wit_20.
Axiom proof_of_sort_safety_wit_21 : sort_safety_wit_21.
Axiom proof_of_sort_safety_wit_22 : sort_safety_wit_22.
Axiom proof_of_sort_safety_wit_23 : sort_safety_wit_23.
Axiom proof_of_sort_safety_wit_24 : sort_safety_wit_24.
Axiom proof_of_sort_safety_wit_25 : sort_safety_wit_25.
Axiom proof_of_sort_safety_wit_26 : sort_safety_wit_26.
Axiom proof_of_sort_safety_wit_27 : sort_safety_wit_27.
Axiom proof_of_sort_safety_wit_28 : sort_safety_wit_28.
Axiom proof_of_sort_safety_wit_29 : sort_safety_wit_29.
Axiom proof_of_sort_safety_wit_30 : sort_safety_wit_30.
Axiom proof_of_sort_safety_wit_31 : sort_safety_wit_31.
Axiom proof_of_sort_safety_wit_32 : sort_safety_wit_32.
Axiom proof_of_sort_safety_wit_33 : sort_safety_wit_33.
Axiom proof_of_sort_safety_wit_34 : sort_safety_wit_34.
Axiom proof_of_sort_safety_wit_35 : sort_safety_wit_35.
Axiom proof_of_sort_safety_wit_36 : sort_safety_wit_36.
Axiom proof_of_sort_entail_wit_1 : sort_entail_wit_1.
Axiom proof_of_sort_entail_wit_2_1 : sort_entail_wit_2_1.
Axiom proof_of_sort_entail_wit_2_2 : sort_entail_wit_2_2.
Axiom proof_of_sort_entail_wit_3 : sort_entail_wit_3.
Axiom proof_of_sort_entail_wit_4 : sort_entail_wit_4.
Axiom proof_of_sort_entail_wit_5 : sort_entail_wit_5.
Axiom proof_of_sort_entail_wit_6 : sort_entail_wit_6.
Axiom proof_of_sort_entail_wit_7 : sort_entail_wit_7.
Axiom proof_of_sort_entail_wit_8 : sort_entail_wit_8.
Axiom proof_of_sort_entail_wit_9 : sort_entail_wit_9.
Axiom proof_of_sort_entail_wit_10 : sort_entail_wit_10.
Axiom proof_of_sort_entail_wit_11 : sort_entail_wit_11.
Axiom proof_of_sort_entail_wit_12 : sort_entail_wit_12.
Axiom proof_of_sort_entail_wit_13 : sort_entail_wit_13.
Axiom proof_of_sort_entail_wit_14 : sort_entail_wit_14.
Axiom proof_of_sort_entail_wit_15 : sort_entail_wit_15.
Axiom proof_of_sort_entail_wit_16 : sort_entail_wit_16.
Axiom proof_of_sort_return_wit_1 : sort_return_wit_1.
Axiom proof_of_sort_return_wit_2 : sort_return_wit_2.
Axiom proof_of_sort_partial_solve_wit_1 : sort_partial_solve_wit_1.
Axiom proof_of_sort_partial_solve_wit_2 : sort_partial_solve_wit_2.
Axiom proof_of_sort_partial_solve_wit_3 : sort_partial_solve_wit_3.
Axiom proof_of_sort_partial_solve_wit_4 : sort_partial_solve_wit_4.
Axiom proof_of_sort_partial_solve_wit_5 : sort_partial_solve_wit_5.
Axiom proof_of_sort_partial_solve_wit_6 : sort_partial_solve_wit_6.
Axiom proof_of_sort_partial_solve_wit_7 : sort_partial_solve_wit_7.
Axiom proof_of_sort_partial_solve_wit_8 : sort_partial_solve_wit_8.
Axiom proof_of_sort_partial_solve_wit_9 : sort_partial_solve_wit_9.
Axiom proof_of_sort_partial_solve_wit_10 : sort_partial_solve_wit_10.
Axiom proof_of_sort_partial_solve_wit_11 : sort_partial_solve_wit_11.
Axiom proof_of_sort_partial_solve_wit_12 : sort_partial_solve_wit_12.
Axiom proof_of_sort_partial_solve_wit_13 : sort_partial_solve_wit_13.
Axiom proof_of_sort_partial_solve_wit_14 : sort_partial_solve_wit_14.
Axiom proof_of_sort_partial_solve_wit_15 : sort_partial_solve_wit_15.

End VC_Correct.
