From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_lib.
Local Open Scope sac.

(*----- Function llabs -----*)

Definition llabs_safety_wit_1 :=
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)),
  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (x_pre <> (INT64_MIN)) ”
.

Definition llabs_safety_wit_2 :=
forall (x_pre: Z) (PreH1 : ((-10000) <= x_pre)) (PreH2 : (x_pre <= 10000)),
  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition llabs_return_wit_1 :=
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)),
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)),
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
).

Definition llabs_return_wit_1_split_goal_1 :=
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)),
  ((-x_pre) = (Z.abs (x_pre)))
.

Definition llabs_return_wit_2 :=
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)),
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)),
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
).

Definition llabs_return_wit_2_split_goal_1 :=
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)),
  (x_pre = (Z.abs (x_pre)))
.

(*----- Function gcdll -----*)

Definition gcdll_safety_wit_1 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  ((( &( "r" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "b" ) )) # Int64  |-> b)
|--
  “ ((a <> (INT64_MIN)) \/ (b <> (-1))) ”
  &&  “ (b <> 0) ”
.

Definition gcdll_safety_wit_2 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b = 0)),
  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "b" ) )) # Int64  |-> b)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gcdll_safety_wit_3 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a < 0)) (PreH2 : (1 <= a)) (PreH3 : (a <= 10000)) (PreH4 : (0 <= b)) (PreH5 : (b <= 10000)) (PreH6 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH7 : (b = 0)),
  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "b" ) )) # Int64  |-> b)
|--
  “ False ”
.

Definition gcdll_entail_wit_1 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (1 <= a_pre)) (PreH2 : (a_pre <= 10000)) (PreH3 : (1 <= b_pre)) (PreH4 : (b_pre <= 10000)),
  TT && emp 
|--
  “ (1 <= a_pre) ”
  &&  “ (a_pre <= 10000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 10000) ”
  &&  “ ((GcdValue (a_pre) (b_pre)) = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
.

Definition gcdll_entail_wit_2 :=
(
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  TT && emp 
|--
  “ (1 <= b) ”
  &&  “ (b <= 10000) ”
  &&  “ (0 <= (a % ( b ) )) ”
  &&  “ ((a % ( b ) ) <= 10000) ”
  &&  “ ((GcdValue (b) ((a % ( b ) ))) = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  TT && emp 
|--
  “ ((GcdValue (b) ((a % ( b ) ))) = (GcdValue (a_pre) (b_pre))) ”
  &&  “ ((a % ( b ) ) <= 10000) ”
  &&  “ (0 <= (a % ( b ) )) ”
  &&  emp
).

Definition gcdll_entail_wit_2_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  ((GcdValue (b) ((a % ( b ) ))) = (GcdValue (a_pre) (b_pre)))
.

Definition gcdll_entail_wit_2_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  ((a % ( b ) ) <= 10000)
.

Definition gcdll_entail_wit_2_split_goal_3 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  (0 <= (a % ( b ) ))
.

Definition gcdll_return_wit_1 :=
(
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a >= 0)) (PreH2 : (1 <= a)) (PreH3 : (a <= 10000)) (PreH4 : (0 <= b)) (PreH5 : (b <= 10000)) (PreH6 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH7 : (b = 0)),
  TT && emp 
|--
  “ (a = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a >= 0)) (PreH2 : (1 <= a)) (PreH3 : (a <= 10000)) (PreH4 : (0 <= b)) (PreH5 : (b <= 10000)) (PreH6 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH7 : (b = 0)),
  TT && emp 
|--
  “ (a = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
).

Definition gcdll_return_wit_1_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a >= 0)) (PreH2 : (1 <= a)) (PreH3 : (a <= 10000)) (PreH4 : (0 <= b)) (PreH5 : (b <= 10000)) (PreH6 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH7 : (b = 0)),
  (a = (GcdValue (a_pre) (b_pre)))
.

(*----- Function pair_fill -----*)

Definition pair_fill_safety_wit_1 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |-> retval_3)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pair_fill_safety_wit_2 :=
(
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |-> retval)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ ((b_pre <> (INT64_MIN)) \/ (retval <> (-1))) ”
  &&  “ (retval <> 0) ”
) \/
(
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |-> retval)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ ((b_pre <> (INT64_MIN)) \/ (retval <> (-1))) ”
  &&  “ (retval <> 0) ”
).

Definition pair_fill_safety_wit_2_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |-> retval)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ ((b_pre <> (INT64_MIN)) \/ (retval <> (-1))) ”
.

Definition pair_fill_safety_wit_2_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |-> retval)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ (retval <> 0) ”
.

Definition pair_fill_safety_wit_3 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> (b_pre ÷ retval_3 ))
  **  (Int64Array.undef_seg out_pre 1 2 )
  **  ((( &( "g" ) )) # Int64  |-> retval_3)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pair_fill_safety_wit_4 :=
(
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> (b_pre ÷ retval ))
  **  (Int64Array.undef_seg out_pre 1 2 )
  **  ((( &( "g" ) )) # Int64  |-> retval)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (((-a_pre) <> (INT64_MIN)) \/ (retval <> (-1))) ”
  &&  “ (retval <> 0) ”
) \/
(
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> (b_pre ÷ retval ))
  **  (Int64Array.undef_seg out_pre 1 2 )
  **  ((( &( "g" ) )) # Int64  |-> retval)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (((-a_pre) <> (INT64_MIN)) \/ (retval <> (-1))) ”
  &&  “ (retval <> 0) ”
).

Definition pair_fill_safety_wit_4_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> (b_pre ÷ retval ))
  **  (Int64Array.undef_seg out_pre 1 2 )
  **  ((( &( "g" ) )) # Int64  |-> retval)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (((-a_pre) <> (INT64_MIN)) \/ (retval <> (-1))) ”
.

Definition pair_fill_safety_wit_4_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> (b_pre ÷ retval ))
  **  (Int64Array.undef_seg out_pre 1 2 )
  **  ((( &( "g" ) )) # Int64  |-> retval)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (retval <> 0) ”
.

Definition pair_fill_safety_wit_5 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> (b_pre ÷ retval_3 ))
  **  (Int64Array.undef_seg out_pre 1 2 )
  **  ((( &( "g" ) )) # Int64  |-> retval_3)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (a_pre <> (INT64_MIN)) ”
.

Definition pair_fill_return_wit_1 :=
(
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  (((out_pre + (1 * sizeof(INT64)))) # Int64  |-> ((-a_pre) ÷ retval_3 ))
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> (b_pre ÷ retval_3 ))
|--
  EX (pair_out: (@list Z)),
  “ (OutputPrefix (cons (a_pre) ((cons (b_pre) ((@nil Z))))) pair_out 0 ) ”
  &&  (Int64Array.full out_pre 2 pair_out )
) \/
(
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((b_pre ÷ retval_3 ) <= INT64_MAX)) (PreH2 : (((-a_pre) ÷ retval_3 ) <= INT64_MAX)) (PreH3 : ((b_pre ÷ retval_3 ) >= INT64_MIN)) (PreH4 : (((-a_pre) ÷ retval_3 ) >= INT64_MIN)) (PreH5 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH6 : (retval_2 = (Z.abs (b_pre)))) (PreH7 : (retval = (Z.abs (a_pre)))) (PreH8 : ((-10000) <= a_pre)) (PreH9 : (a_pre <= 10000)) (PreH10 : (a_pre <> 0)) (PreH11 : ((-10000) <= b_pre)) (PreH12 : (b_pre <= 10000)) (PreH13 : (b_pre <> 0)),
  (((out_pre + (1 * sizeof(INT64)))) # Int64  |-> ((-a_pre) ÷ retval_3 ))
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> (b_pre ÷ retval_3 ))
|--
  EX (pair_out: (@list Z)),
  “ (OutputPrefix (cons (a_pre) ((cons (b_pre) ((@nil Z))))) pair_out 0 ) ”
  &&  (Int64Array.full out_pre 2 pair_out )
).

Definition pair_fill_partial_solve_wit_1_pure :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (PreH1 : ((-10000) <= a_pre)) (PreH2 : (a_pre <= 10000)) (PreH3 : (a_pre <> 0)) (PreH4 : ((-10000) <= b_pre)) (PreH5 : (b_pre <= 10000)) (PreH6 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ ((-10000) <= a_pre) ”
  &&  “ (a_pre <= 10000) ”
.

Definition pair_fill_partial_solve_wit_1_aux :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (PreH1 : ((-10000) <= a_pre)) (PreH2 : (a_pre <= 10000)) (PreH3 : (a_pre <> 0)) (PreH4 : ((-10000) <= b_pre)) (PreH5 : (b_pre <= 10000)) (PreH6 : (b_pre <> 0)),
  (Int64Array.undef_full out_pre 2 )
|--
  “ ((-10000) <= a_pre) ”
  &&  “ (a_pre <= 10000) ”
  &&  “ ((-10000) <= a_pre) ”
  &&  “ (a_pre <= 10000) ”
  &&  “ (a_pre <> 0) ”
  &&  “ ((-10000) <= b_pre) ”
  &&  “ (b_pre <= 10000) ”
  &&  “ (b_pre <> 0) ”
  &&  (Int64Array.undef_full out_pre 2 )
.

Definition pair_fill_partial_solve_wit_1 := pair_fill_partial_solve_wit_1_pure -> pair_fill_partial_solve_wit_1_aux.

Definition pair_fill_partial_solve_wit_2_pure :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs (a_pre)))) (PreH2 : ((-10000) <= a_pre)) (PreH3 : (a_pre <= 10000)) (PreH4 : (a_pre <> 0)) (PreH5 : ((-10000) <= b_pre)) (PreH6 : (b_pre <= 10000)) (PreH7 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ ((-10000) <= b_pre) ”
  &&  “ (b_pre <= 10000) ”
.

Definition pair_fill_partial_solve_wit_2_aux :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs (a_pre)))) (PreH2 : ((-10000) <= a_pre)) (PreH3 : (a_pre <= 10000)) (PreH4 : (a_pre <> 0)) (PreH5 : ((-10000) <= b_pre)) (PreH6 : (b_pre <= 10000)) (PreH7 : (b_pre <> 0)),
  (Int64Array.undef_full out_pre 2 )
|--
  “ ((-10000) <= b_pre) ”
  &&  “ (b_pre <= 10000) ”
  &&  “ (retval = (Z.abs (a_pre))) ”
  &&  “ ((-10000) <= a_pre) ”
  &&  “ (a_pre <= 10000) ”
  &&  “ (a_pre <> 0) ”
  &&  “ ((-10000) <= b_pre) ”
  &&  “ (b_pre <= 10000) ”
  &&  “ (b_pre <> 0) ”
  &&  (Int64Array.undef_full out_pre 2 )
.

Definition pair_fill_partial_solve_wit_2 := pair_fill_partial_solve_wit_2_pure -> pair_fill_partial_solve_wit_2_aux.

Definition pair_fill_partial_solve_wit_3_pure :=
(
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Z.abs (b_pre)))) (PreH2 : (retval = (Z.abs (a_pre)))) (PreH3 : ((-10000) <= a_pre)) (PreH4 : (a_pre <= 10000)) (PreH5 : (a_pre <> 0)) (PreH6 : ((-10000) <= b_pre)) (PreH7 : (b_pre <= 10000)) (PreH8 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ (retval_2 <= 10000) ”
  &&  “ (1 <= retval_2) ”
  &&  “ (retval <= 10000) ”
  &&  “ (1 <= retval) ”
) \/
(
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (b_pre <= INT64_MAX)) (PreH2 : (a_pre <= INT64_MAX)) (PreH3 : (b_pre >= INT64_MIN)) (PreH4 : (a_pre >= INT64_MIN)) (PreH5 : (retval_2 = (Z.abs (b_pre)))) (PreH6 : (retval = (Z.abs (a_pre)))) (PreH7 : ((-10000) <= a_pre)) (PreH8 : (a_pre <= 10000)) (PreH9 : (a_pre <> 0)) (PreH10 : ((-10000) <= b_pre)) (PreH11 : (b_pre <= 10000)) (PreH12 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ (1 <= retval) ”
  &&  “ (retval <= 10000) ”
  &&  “ (1 <= retval_2) ”
  &&  “ (retval_2 <= 10000) ”
).

Definition pair_fill_partial_solve_wit_3_pure_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (b_pre <= INT64_MAX)) (PreH2 : (a_pre <= INT64_MAX)) (PreH3 : (b_pre >= INT64_MIN)) (PreH4 : (a_pre >= INT64_MIN)) (PreH5 : (retval_2 = (Z.abs (b_pre)))) (PreH6 : (retval = (Z.abs (a_pre)))) (PreH7 : ((-10000) <= a_pre)) (PreH8 : (a_pre <= 10000)) (PreH9 : (a_pre <> 0)) (PreH10 : ((-10000) <= b_pre)) (PreH11 : (b_pre <= 10000)) (PreH12 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ (1 <= retval) ”
.

Definition pair_fill_partial_solve_wit_3_pure_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (b_pre <= INT64_MAX)) (PreH2 : (a_pre <= INT64_MAX)) (PreH3 : (b_pre >= INT64_MIN)) (PreH4 : (a_pre >= INT64_MIN)) (PreH5 : (retval_2 = (Z.abs (b_pre)))) (PreH6 : (retval = (Z.abs (a_pre)))) (PreH7 : ((-10000) <= a_pre)) (PreH8 : (a_pre <= 10000)) (PreH9 : (a_pre <> 0)) (PreH10 : ((-10000) <= b_pre)) (PreH11 : (b_pre <= 10000)) (PreH12 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ (retval <= 10000) ”
.

Definition pair_fill_partial_solve_wit_3_pure_split_goal_3 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (b_pre <= INT64_MAX)) (PreH2 : (a_pre <= INT64_MAX)) (PreH3 : (b_pre >= INT64_MIN)) (PreH4 : (a_pre >= INT64_MIN)) (PreH5 : (retval_2 = (Z.abs (b_pre)))) (PreH6 : (retval = (Z.abs (a_pre)))) (PreH7 : ((-10000) <= a_pre)) (PreH8 : (a_pre <= 10000)) (PreH9 : (a_pre <> 0)) (PreH10 : ((-10000) <= b_pre)) (PreH11 : (b_pre <= 10000)) (PreH12 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ (1 <= retval_2) ”
.

Definition pair_fill_partial_solve_wit_3_pure_split_goal_4 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (b_pre <= INT64_MAX)) (PreH2 : (a_pre <= INT64_MAX)) (PreH3 : (b_pre >= INT64_MIN)) (PreH4 : (a_pre >= INT64_MIN)) (PreH5 : (retval_2 = (Z.abs (b_pre)))) (PreH6 : (retval = (Z.abs (a_pre)))) (PreH7 : ((-10000) <= a_pre)) (PreH8 : (a_pre <= 10000)) (PreH9 : (a_pre <> 0)) (PreH10 : ((-10000) <= b_pre)) (PreH11 : (b_pre <= 10000)) (PreH12 : (b_pre <> 0)),
  ((( &( "g" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 2 )
|--
  “ (retval_2 <= 10000) ”
.

Definition pair_fill_partial_solve_wit_3_aux :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Z.abs (b_pre)))) (PreH2 : (retval = (Z.abs (a_pre)))) (PreH3 : ((-10000) <= a_pre)) (PreH4 : (a_pre <= 10000)) (PreH5 : (a_pre <> 0)) (PreH6 : ((-10000) <= b_pre)) (PreH7 : (b_pre <= 10000)) (PreH8 : (b_pre <> 0)),
  (Int64Array.undef_full out_pre 2 )
|--
  “ (retval_2 <= 10000) ”
  &&  “ (1 <= retval_2) ”
  &&  “ (retval <= 10000) ”
  &&  “ (1 <= retval) ”
  &&  “ (retval_2 = (Z.abs (b_pre))) ”
  &&  “ (retval = (Z.abs (a_pre))) ”
  &&  “ ((-10000) <= a_pre) ”
  &&  “ (a_pre <= 10000) ”
  &&  “ (a_pre <> 0) ”
  &&  “ ((-10000) <= b_pre) ”
  &&  “ (b_pre <= 10000) ”
  &&  “ (b_pre <> 0) ”
  &&  (Int64Array.undef_full out_pre 2 )
.

Definition pair_fill_partial_solve_wit_3 := pair_fill_partial_solve_wit_3_pure -> pair_fill_partial_solve_wit_3_aux.

Definition pair_fill_partial_solve_wit_4 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  (Int64Array.undef_full out_pre 2 )
|--
  “ (retval_3 = (GcdValue (retval) (retval_2))) ”
  &&  “ (retval_2 = (Z.abs (b_pre))) ”
  &&  “ (retval = (Z.abs (a_pre))) ”
  &&  “ ((-10000) <= a_pre) ”
  &&  “ (a_pre <= 10000) ”
  &&  “ (a_pre <> 0) ”
  &&  “ ((-10000) <= b_pre) ”
  &&  “ (b_pre <= 10000) ”
  &&  “ (b_pre <> 0) ”
  &&  (((out_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg out_pre 1 2 )
.

Definition pair_fill_partial_solve_wit_5 :=
forall (a_pre: Z) (b_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre <> 0)) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre <> 0)),
  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> (b_pre ÷ retval_3 ))
  **  (Int64Array.undef_seg out_pre 1 2 )
|--
  “ (retval_3 = (GcdValue (retval) (retval_2))) ”
  &&  “ (retval_2 = (Z.abs (b_pre))) ”
  &&  “ (retval = (Z.abs (a_pre))) ”
  &&  “ ((-10000) <= a_pre) ”
  &&  “ (a_pre <= 10000) ”
  &&  “ (a_pre <> 0) ”
  &&  “ ((-10000) <= b_pre) ”
  &&  “ (b_pre <= 10000) ”
  &&  “ (b_pre <> 0) ”
  &&  (((out_pre + (1 * sizeof(INT64)))) # Int64  |->_)
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> (b_pre ÷ retval_3 ))
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ ((n_pre <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((n_pre % ( 2 ) ) <> 0)),
  ((( &( "z" ) )) # Int64  |->_)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((n_pre % ( 2 ) ) <> 0)),
  ((( &( "y" ) )) # Int64  |->_)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((n_pre % ( 2 ) ) <> 0)),
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (((Znth 0 values 0) + (Znth 1 values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth 0 values 0) + (Znth 1 values 0) )) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (Int64Array.undef_seg b_pre 1 n_pre )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (((b_pre + (1 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (Int64Array.undef_seg b_pre (1 + 1 ) n_pre )
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (((b_pre + (1 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (Int64Array.undef_seg b_pre (1 + 1 ) n_pre )
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (((Znth 0 values 0) + (Znth 1 values 0) ) <> (INT64_MIN)) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (((b_pre + (1 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (Int64Array.undef_seg b_pre (1 + 1 ) n_pre )
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (((Znth 0 values 0) + (Znth 1 values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth 0 values 0) + (Znth 1 values 0) )) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (((Znth 0 values 0) + (Znth 2 values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth 0 values 0) + (Znth 2 values 0) )) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 1 values 0))
  **  (Int64Array.undef_seg b_pre 1 n_pre )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  “ ((x + z ) <> (INT64_MIN)) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  “ ((x + z ) <> (INT64_MIN)) ”
).

Definition solver_safety_wit_19_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  “ ((x + z ) <> (INT64_MIN)) ”
.

Definition solver_safety_wit_20 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  “ ((x + z ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (x + z )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  “ ((x + z ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (x + z )) ”
).

Definition solver_safety_wit_20_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  “ ((x + z ) <= INT64_MAX) ”
.

Definition solver_safety_wit_20_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  “ ((INT64_MIN) <= (x + z )) ”
.

Definition solver_safety_wit_21 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_full b_pre n_pre (replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_23 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_full b_pre n_pre (replace_Znth (2) ((Some ((Znth 0 values 0)))) ((replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_full b_pre n_pre (replace_Znth (2) ((Some ((Znth 0 values 0)))) ((replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (((Znth 1 values 0) + (Znth 2 values 0) ) <> (INT64_MIN)) ”
.

Definition solver_safety_wit_25 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_full b_pre n_pre (replace_Znth (2) ((Some ((Znth 0 values 0)))) ((replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (((Znth 1 values 0) + (Znth 2 values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth 1 values 0) + (Znth 2 values 0) )) ”
.

Definition solver_safety_wit_26 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.undef_seg b_pre ((1 + 1 ) + 1 ) n_pre )
  **  (((b_pre + (2 * sizeof(INT64)))) # Int64  |-> (-((Znth 0 values 0) + (Znth 1 values 0) )))
  **  (((b_pre + (1 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_27 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  (Int64Array.seg b_pre 0 (1 + 1 ) (app ((cons (y) ((@nil Z)))) ((cons ((-(x + z ))) ((@nil Z))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_28 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_full b_pre n_pre (replace_Znth (0) ((Some ((-((Znth 1 values 0) + (Znth 2 values 0) ))))) ((replace_Znth (2) ((Some ((Znth 0 values 0)))) ((replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))))))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int64  |-> (Znth 2 values 0))
  **  ((( &( "y" ) )) # Int64  |-> (Znth 1 values 0))
  **  ((( &( "x" ) )) # Int64  |-> (Znth 0 values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_29 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (i: Z) (start: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre i n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_30 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (i: Z) (start: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre i n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_31 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (i: Z) (start: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre i n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_32 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (i: Z) (start: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre i n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_33 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_34 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_35 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_36 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_37 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (pair_out: (@list Z)) (PreH1 : (OutputPrefix (cons ((Znth i values 0)) ((cons ((Znth (i + 1 ) values 0)) ((@nil Z))))) pair_out 0 )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH6 : (start = 0)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (Int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ ((i + 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition solver_safety_wit_38 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (pair_out: (@list Z)) (PreH1 : (OutputPrefix (cons ((Znth i values 0)) ((cons ((Znth (i + 1 ) values 0)) ((@nil Z))))) pair_out 0 )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH6 : (start = 0)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (Int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_39 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (pair_out: (@list Z)) (PreH1 : (OutputPrefix (cons ((Znth i values 0)) ((cons ((Znth (i + 1 ) values 0)) ((@nil Z))))) pair_out 0 )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH6 : (start = 3)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (Int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ ((i + 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition solver_safety_wit_40 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (pair_out: (@list Z)) (PreH1 : (OutputPrefix (cons ((Znth i values 0)) ((cons ((Znth (i + 1 ) values 0)) ((@nil Z))))) pair_out 0 )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH6 : (start = 3)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (Int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)),
  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (n_pre >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  TT && emp 
|--
  “ (3 <= n_pre) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (n_pre >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (3 <= n_pre)
.

Definition solver_entail_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_seg b_pre 1 n_pre (replace_Znth ((2 - 1 )) ((Some ((Znth 1 values 0)))) ((repeat_Z (None) ((n_pre - 1 ))))) )
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 1 values 0))
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 = 0) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ ((Znth 0 values 0) = (Znth 0 values 0)) ”
  &&  “ ((Znth 1 values 0) = (Znth 1 values 0)) ”
  &&  “ ((Znth 2 values 0) = (Znth 2 values 0)) ”
  &&  “ (((Znth 0 values 0) + (Znth 1 values 0) ) = 0) ”
  &&  “ (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons ((Znth 1 values 0)) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons ((Znth 1 values 0)) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (PreH1 : ((Znth 1 values 0) <= INT64_MAX)) (PreH2 : ((Znth 1 values 0) >= INT64_MIN)) (PreH3 : (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0)) (PreH4 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH5 : (3 <= n_pre)) (PreH6 : (0 <= INT_MAX)) (PreH7 : (0 >= INT_MIN)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_seg b_pre 1 n_pre (replace_Znth ((2 - 1 )) ((Some ((Znth 1 values 0)))) ((repeat_Z (None) ((n_pre - 1 ))))) )
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 1 values 0))
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  (Int64Array.seg b_pre 0 1 (cons ((Znth 1 values 0)) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons ((Znth 1 values 0)) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (PreH1 : ((Znth 1 values 0) <= INT64_MAX)) (PreH2 : ((Znth 1 values 0) >= INT64_MIN)) (PreH3 : (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0)) (PreH4 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH5 : (3 <= n_pre)) (PreH6 : (0 <= INT_MAX)) (PreH7 : (0 >= INT_MIN)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_seg b_pre 1 n_pre (replace_Znth ((2 - 1 )) ((Some ((Znth 1 values 0)))) ((repeat_Z (None) ((n_pre - 1 ))))) )
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 1 values 0))
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
.

Definition solver_entail_wit_2_split_goal_spatial :=
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (PreH1 : ((Znth 1 values 0) <= INT64_MAX)) (PreH2 : ((Znth 1 values 0) >= INT64_MIN)) (PreH3 : (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0)) (PreH4 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH5 : (3 <= n_pre)) (PreH6 : (0 <= INT_MAX)) (PreH7 : (0 >= INT_MIN)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_seg b_pre 1 n_pre (replace_Znth ((2 - 1 )) ((Some ((Znth 1 values 0)))) ((repeat_Z (None) ((n_pre - 1 ))))) )
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 1 values 0))
|--
  (Int64Array.seg b_pre 0 1 (cons ((Znth 1 values 0)) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons ((Znth 1 values 0)) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
.

Definition solver_entail_wit_3_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.undef_seg b_pre ((1 + 1 ) + 1 ) n_pre )
  **  (((b_pre + (2 * sizeof(INT64)))) # Int64  |-> (-((Znth 0 values 0) + (Znth 1 values 0) )))
  **  (((b_pre + (1 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (IntArray.full a_pre n_pre values )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (3 = 3) ”
  &&  “ (0 <= 3) ”
  &&  “ (3 <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (3 % ( 2 ) )) ”
  &&  “ (OutputPrefix (sublist (0) (3) (values)) written ((10000 * 3 ) ÷ 3 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 3 written )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (PreH1 : ((Znth 2 values 0) <= INT64_MAX)) (PreH2 : ((-((Znth 0 values 0) + (Znth 1 values 0) )) <= INT64_MAX)) (PreH3 : ((Znth 2 values 0) >= INT64_MIN)) (PreH4 : ((-((Znth 0 values 0) + (Znth 1 values 0) )) >= INT64_MIN)) (PreH5 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH6 : (3 <= n_pre)) (PreH7 : (0 <= INT_MAX)) (PreH8 : (0 >= INT_MIN)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : ((n_pre % ( 2 ) ) <> 0)),
  (((b_pre + (2 * sizeof(INT64)))) # Int64  |-> (-((Znth 0 values 0) + (Znth 1 values 0) )))
  **  (((b_pre + (1 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (0 <= 3) ”
  &&  “ (3 <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (3 % ( 2 ) )) ”
  &&  “ (OutputPrefix (sublist (0) (3) (values)) written ((10000 * 3 ) ÷ 3 ) ) ”
  &&  (Int64Array.seg b_pre 0 3 written )
).

Definition solver_entail_wit_3_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  (Int64Array.seg b_pre 0 (1 + 1 ) (app ((cons (y) ((@nil Z)))) ((cons ((-(x + z ))) ((@nil Z))))) )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (3 = 3) ”
  &&  “ (0 <= 3) ”
  &&  “ (3 <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (3 % ( 2 ) )) ”
  &&  “ (OutputPrefix (sublist (0) (3) (values)) written ((10000 * 3 ) ÷ 3 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 3 written )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  (Int64Array.seg b_pre 0 (1 + 1 ) (app ((cons (y) ((@nil Z)))) ((cons ((-(x + z ))) ((@nil Z))))) )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (0 <= 3) ”
  &&  “ (3 <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (3 % ( 2 ) )) ”
  &&  “ (OutputPrefix (sublist (0) (3) (values)) written ((10000 * 3 ) ÷ 3 ) ) ”
  &&  (Int64Array.seg b_pre 0 3 written )
).

Definition solver_entail_wit_3_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_full b_pre n_pre (replace_Znth (0) ((Some ((-((Znth 1 values 0) + (Znth 2 values 0) ))))) ((replace_Znth (2) ((Some ((Znth 0 values 0)))) ((replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))))))) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (3 = 3) ”
  &&  “ (0 <= 3) ”
  &&  “ (3 <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (3 % ( 2 ) )) ”
  &&  “ (OutputPrefix (sublist (0) (3) (values)) written ((10000 * 3 ) ÷ 3 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 3 written )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_full b_pre n_pre (replace_Znth (0) ((Some ((-((Znth 1 values 0) + (Znth 2 values 0) ))))) ((replace_Znth (2) ((Some ((Znth 0 values 0)))) ((replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))))))) )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (0 <= 3) ”
  &&  “ (3 <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (3 % ( 2 ) )) ”
  &&  “ (OutputPrefix (sublist (0) (3) (values)) written ((10000 * 3 ) ÷ 3 ) ) ”
  &&  (Int64Array.seg b_pre 0 3 written )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
).

Definition solver_entail_wit_3_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (0 = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (0 % ( 2 ) )) ”
  &&  “ (OutputPrefix (sublist (0) (0) (values)) written ((10000 * 0 ) ÷ 3 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 0 written )
  **  (Int64Array.undef_seg b_pre 0 n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) = 0)),
  TT && emp 
|--
  “ (OutputPrefix (sublist (0) (0) (values)) (@nil Z) ((10000 * 0 ) ÷ 3 ) ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  emp
).

Definition solver_entail_wit_3_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) = 0)),
  (OutputPrefix (sublist (0) (0) (values)) (@nil Z) ((10000 * 0 ) ÷ 3 ) )
.

Definition solver_entail_wit_3_4_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) = 0)),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))
.

Definition solver_entail_wit_4_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (start: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH9 : (OutputPrefix (sublist (0) (start) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 start written_2 )
  **  (Int64Array.undef_seg b_pre start n_pre )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 0) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= start) ”
  &&  “ (start <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ (((start - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) (start) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 start written )
  **  (Int64Array.undef_seg b_pre start n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (written_2: (@list Z)) (start: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH9 : (OutputPrefix (sublist (0) (start) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  TT && emp 
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (written_2: (@list Z)) (start: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH9 : (OutputPrefix (sublist (0) (start) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))
.

Definition solver_entail_wit_4_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (start: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH9 : (OutputPrefix (sublist (0) (start) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 start written_2 )
  **  (Int64Array.undef_seg b_pre start n_pre )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 3) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= start) ”
  &&  “ (start <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ (((start - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) (start) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 start written )
  **  (Int64Array.undef_seg b_pre start n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (written_2: (@list Z)) (start: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH9 : (OutputPrefix (sublist (0) (start) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  TT && emp 
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (written_2: (@list Z)) (start: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH9 : (OutputPrefix (sublist (0) (start) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))
.

Definition solver_entail_wit_5_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 0)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written_2 )
  **  (Int64Array.undef_seg b_pre i n_pre )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 0) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ (((i - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 0)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (Int64Array.undef_seg b_pre i n_pre )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
).

Definition solver_entail_wit_5_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 0)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (Int64Array.undef_seg b_pre i n_pre )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
.

Definition solver_entail_wit_5_1_split_goal_spatial :=
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 0)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (Int64Array.undef_seg b_pre i n_pre )
|--
  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
.

Definition solver_entail_wit_5_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 3)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written_2 )
  **  (Int64Array.undef_seg b_pre i n_pre )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 3) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ (((i - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 3)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (Int64Array.undef_seg b_pre i n_pre )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
).

Definition solver_entail_wit_5_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 3)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (Int64Array.undef_seg b_pre i n_pre )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
.

Definition solver_entail_wit_5_2_split_goal_spatial :=
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 3)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (Int64Array.undef_seg b_pre i n_pre )
|--
  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
.

Definition solver_entail_wit_6_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (start: Z) (i: Z) (pair_out: (@list Z)) (PreH1 : (OutputPrefix (cons ((Znth i values 0)) ((cons ((Znth (i + 1 ) values 0)) ((@nil Z))))) pair_out 0 )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 0)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (Int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written_2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 0) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= (i + 2 )) ”
  &&  “ ((i + 2 ) <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ ((((i + 2 ) - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) ((i + 2 )) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 (i + 2 ) written )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (start: Z) (i: Z) (pair_out: (@list Z)) (PreH1 : (OutputPrefix (cons ((Znth i values 0)) ((cons ((Znth (i + 1 ) values 0)) ((@nil Z))))) pair_out 0 )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 0)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (Int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out )
  **  (Int64Array.seg b_pre 0 i written_2 )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 0) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= (i + 2 )) ”
  &&  “ ((i + 2 ) <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ ((((i + 2 ) - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) ((i + 2 )) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (Int64Array.seg b_pre 0 (i + 2 ) written )
).

Definition solver_entail_wit_6_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (start: Z) (i: Z) (pair_out: (@list Z)) (PreH1 : (OutputPrefix (cons ((Znth i values 0)) ((cons ((Znth (i + 1 ) values 0)) ((@nil Z))))) pair_out 0 )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 3)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (Int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written_2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 3) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= (i + 2 )) ”
  &&  “ ((i + 2 ) <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ ((((i + 2 ) - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) ((i + 2 )) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 (i + 2 ) written )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (written_2: (@list Z)) (start: Z) (i: Z) (pair_out: (@list Z)) (PreH1 : (OutputPrefix (cons ((Znth i values 0)) ((cons ((Znth (i + 1 ) values 0)) ((@nil Z))))) pair_out 0 )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 10000)) /\ ((Znth j_2 values 0) <> 0)))) (PreH6 : (start = 3)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written_2 ((10000 * start ) ÷ 3 ) )),
  (Int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out )
  **  (Int64Array.seg b_pre 0 i written_2 )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 3) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= (i + 2 )) ”
  &&  “ ((i + 2 ) <= n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ ((((i + 2 ) - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) ((i + 2 )) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (Int64Array.seg b_pre 0 (i + 2 ) written )
).

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH6 : (start = 0)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre i n_pre )
|--
  EX (out: (@list Z)),
  “ (Spec values out ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full b_pre n_pre out )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH6 : (start = 0)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre i n_pre )
|--
  EX (out: (@list Z)),
  “ (Spec values out ) ”
  &&  (Int64Array.full b_pre n_pre out )
).

Definition solver_return_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH6 : (start = 3)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre i n_pre )
|--
  EX (out: (@list Z)),
  “ (Spec values out ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full b_pre n_pre out )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (i: Z) (start: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH6 : (start = 3)) (PreH7 : (0 <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH11 : (((i - start ) % ( 2 ) ) = 0)) (PreH12 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre i n_pre )
|--
  EX (out: (@list Z)),
  “ (Spec values out ) ”
  &&  (Int64Array.full b_pre n_pre out )
).

Definition solver_partial_solve_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((a_pre + (2 * sizeof(INT)))) # Int  |-> (Znth 2 values 0))
  **  (IntArray.missing_i a_pre 2 0 n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((a_pre + (1 * sizeof(INT)))) # Int  |-> (Znth 1 values 0))
  **  (IntArray.missing_i a_pre 1 0 n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((a_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 values 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
.

Definition solver_partial_solve_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((b_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg b_pre 1 n_pre )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (Int64Array.undef_seg b_pre 1 n_pre )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((b_pre + (1 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg b_pre (1 + 1 ) n_pre )
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((n_pre % ( 2 ) ) <> 0)),
  (((b_pre + (1 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (Int64Array.undef_seg b_pre (1 + 1 ) n_pre )
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (IntArray.full a_pre n_pre values )
|--
  “ (((Znth 0 values 0) + (Znth 1 values 0) ) <> 0) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((b_pre + (2 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i b_pre 2 (1 + 1 ) n_pre )
  **  (((b_pre + (1 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 2 values 0))
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0) ”
  &&  “ (((Znth 0 values 0) + (Znth 1 values 0) ) = 0) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((b_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg b_pre 1 n_pre )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 1 values 0))
  **  (Int64Array.undef_seg b_pre 1 n_pre )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (((Znth 0 values 0) + (Znth 2 values 0) ) <> 0) ”
  &&  “ (((Znth 0 values 0) + (Znth 1 values 0) ) = 0) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((b_pre + (2 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i b_pre 2 1 n_pre )
  **  (((b_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 1 values 0))
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (start: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (start = 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((n_pre % ( 2 ) ) <> 0)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH7 : (x = (Znth 0 values 0))) (PreH8 : (y = (Znth 1 values 0))) (PreH9 : (z = (Znth 2 values 0))) (PreH10 : ((x + y ) = 0)) (PreH11 : ((x + z ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 1 2 )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
|--
  “ (start = 0) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (x = (Znth 0 values 0)) ”
  &&  “ (y = (Znth 1 values 0)) ”
  &&  “ (z = (Znth 2 values 0)) ”
  &&  “ ((x + y ) = 0) ”
  &&  “ ((x + z ) <> 0) ”
  &&  (((b_pre + (1 * sizeof(INT64)))) # Int64  |->_)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 1 (cons (y) ((@nil Z))) )
  **  (Int64Array.seg b_pre 2 3 (cons (y) ((@nil Z))) )
  **  (Int64Array.undef_seg b_pre 3 n_pre )
.

Definition solver_partial_solve_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.undef_full b_pre n_pre )
|--
  “ (((Znth 0 values 0) + (Znth 2 values 0) ) = 0) ”
  &&  “ (((Znth 0 values 0) + (Znth 1 values 0) ) = 0) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((b_pre + (1 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i b_pre 1 0 n_pre )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_full b_pre n_pre (replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))) )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (((Znth 0 values 0) + (Znth 2 values 0) ) = 0) ”
  &&  “ (((Znth 0 values 0) + (Znth 1 values 0) ) = 0) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((b_pre + (2 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.mixed_missing_i b_pre 2 0 n_pre (replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))) )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (((Znth 0 values 0) + (Znth 2 values 0) ) = 0)) (PreH2 : (((Znth 0 values 0) + (Znth 1 values 0) ) = 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((n_pre % ( 2 ) ) <> 0)),
  (Int64Array.mixed_full b_pre n_pre (replace_Znth (2) ((Some ((Znth 0 values 0)))) ((replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))))) )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (((Znth 0 values 0) + (Znth 2 values 0) ) = 0) ”
  &&  “ (((Znth 0 values 0) + (Znth 1 values 0) ) = 0) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (0 >= INT_MIN) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)) /\ ((Znth i values 0) <> 0))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  (((b_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.mixed_missing_i b_pre 0 0 n_pre (replace_Znth (2) ((Some ((Znth 0 values 0)))) ((replace_Znth (1) ((Some ((Znth 0 values 0)))) ((repeat_Z (None) (n_pre)))))) )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 0) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ (((i - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
.

Definition solver_partial_solve_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 0) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ (((i - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (((a_pre + ((i + 1 ) * sizeof(INT)))) # Int  |-> (Znth (i + 1 ) values 0))
  **  (IntArray.missing_i a_pre (i + 1 ) 0 n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
.

Definition solver_partial_solve_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 3) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ (((i - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
.

Definition solver_partial_solve_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 3) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ (((i - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (((a_pre + ((i + 1 ) * sizeof(INT)))) # Int  |-> (Znth (i + 1 ) values 0))
  **  (IntArray.missing_i a_pre (i + 1 ) 0 n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
.

Definition solver_partial_solve_wit_17_pure :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ ((-10000) <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 10000) ”
  &&  “ ((Znth i values 0) <> 0) ”
  &&  “ ((-10000) <= (Znth (i + 1 ) values 0)) ”
  &&  “ ((Znth (i + 1 ) values 0) <= 10000) ”
  &&  “ ((Znth (i + 1 ) values 0) <> 0) ”
.

Definition solver_partial_solve_wit_17_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 0)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ ((-10000) <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 10000) ”
  &&  “ ((Znth i values 0) <> 0) ”
  &&  “ ((-10000) <= (Znth (i + 1 ) values 0)) ”
  &&  “ ((Znth (i + 1 ) values 0) <= 10000) ”
  &&  “ ((Znth (i + 1 ) values 0) <> 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 0) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ (((i - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
.

Definition solver_partial_solve_wit_17 := solver_partial_solve_wit_17_pure -> solver_partial_solve_wit_17_aux.

Definition solver_partial_solve_wit_18_pure :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ ((-10000) <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 10000) ”
  &&  “ ((Znth i values 0) <> 0) ”
  &&  “ ((-10000) <= (Znth (i + 1 ) values 0)) ”
  &&  “ ((Znth (i + 1 ) values 0) <= 10000) ”
  &&  “ ((Znth (i + 1 ) values 0) <> 0) ”
.

Definition solver_partial_solve_wit_18_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (written: (@list Z)) (start: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0)))) (PreH5 : (start = 3)) (PreH6 : (0 <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((n_pre % ( 2 ) ) = (start % ( 2 ) ))) (PreH10 : (((i - start ) % ( 2 ) ) = 0)) (PreH11 : (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
|--
  “ ((-10000) <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 10000) ”
  &&  “ ((Znth i values 0) <> 0) ”
  &&  “ ((-10000) <= (Znth (i + 1 ) values 0)) ”
  &&  “ ((Znth (i + 1 ) values 0) <= 10000) ”
  &&  “ ((Znth (i + 1 ) values 0) <> 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((((-10000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 10000)) /\ ((Znth j values 0) <> 0))) ”
  &&  “ (start = 3) ”
  &&  “ (0 <= start) ”
  &&  “ (start <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((n_pre % ( 2 ) ) = (start % ( 2 ) )) ”
  &&  “ (((i - start ) % ( 2 ) ) = 0) ”
  &&  “ (OutputPrefix (sublist (0) (i) (values)) written ((10000 * start ) ÷ 3 ) ) ”
  &&  (Int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2 )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg b_pre 0 i written )
  **  (Int64Array.undef_seg b_pre (i + 2 ) n_pre )
.

Definition solver_partial_solve_wit_18 := solver_partial_solve_wit_18_pure -> solver_partial_solve_wit_18_aux.

Module Type VC_Correct.


Axiom proof_of_llabs_safety_wit_1 : llabs_safety_wit_1.
Axiom proof_of_llabs_safety_wit_2 : llabs_safety_wit_2.
Axiom proof_of_llabs_return_wit_1 : llabs_return_wit_1.
Axiom proof_of_llabs_return_wit_2 : llabs_return_wit_2.
Axiom proof_of_gcdll_safety_wit_1 : gcdll_safety_wit_1.
Axiom proof_of_gcdll_safety_wit_2 : gcdll_safety_wit_2.
Axiom proof_of_gcdll_safety_wit_3 : gcdll_safety_wit_3.
Axiom proof_of_gcdll_entail_wit_1 : gcdll_entail_wit_1.
Axiom proof_of_gcdll_entail_wit_2 : gcdll_entail_wit_2.
Axiom proof_of_gcdll_return_wit_1 : gcdll_return_wit_1.
Axiom proof_of_pair_fill_safety_wit_1 : pair_fill_safety_wit_1.
Axiom proof_of_pair_fill_safety_wit_2 : pair_fill_safety_wit_2.
Axiom proof_of_pair_fill_safety_wit_3 : pair_fill_safety_wit_3.
Axiom proof_of_pair_fill_safety_wit_4 : pair_fill_safety_wit_4.
Axiom proof_of_pair_fill_safety_wit_5 : pair_fill_safety_wit_5.
Axiom proof_of_pair_fill_return_wit_1 : pair_fill_return_wit_1.
Axiom proof_of_pair_fill_partial_solve_wit_1_pure : pair_fill_partial_solve_wit_1_pure.
Axiom proof_of_pair_fill_partial_solve_wit_1 : pair_fill_partial_solve_wit_1.
Axiom proof_of_pair_fill_partial_solve_wit_2_pure : pair_fill_partial_solve_wit_2_pure.
Axiom proof_of_pair_fill_partial_solve_wit_2 : pair_fill_partial_solve_wit_2.
Axiom proof_of_pair_fill_partial_solve_wit_3_pure : pair_fill_partial_solve_wit_3_pure.
Axiom proof_of_pair_fill_partial_solve_wit_3 : pair_fill_partial_solve_wit_3.
Axiom proof_of_pair_fill_partial_solve_wit_4 : pair_fill_partial_solve_wit_4.
Axiom proof_of_pair_fill_partial_solve_wit_5 : pair_fill_partial_solve_wit_5.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3.
Axiom proof_of_solver_entail_wit_3_4 : solver_entail_wit_3_4.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
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
Axiom proof_of_solver_partial_solve_wit_17_pure : solver_partial_solve_wit_17_pure.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18_pure : solver_partial_solve_wit_18_pure.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.

End VC_Correct.
