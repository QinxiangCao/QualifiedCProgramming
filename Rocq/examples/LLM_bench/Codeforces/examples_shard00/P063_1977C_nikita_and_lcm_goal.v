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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P063_1977C_nikita_and_lcm_lib.
Local Open Scope sac.

(*----- Function gcdll -----*)

Definition gcdll_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000001)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  ((( &( "t" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "b" ) )) # Int64  |-> b)
|--
  “ ((a <> (INT64_MIN)) \/ (b <> (-1))) ” 
  &&  “ (b <> 0) ”
.

Definition gcdll_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (1 <= a_pre)) (PreH2 : (a_pre <= 1000000001)) (PreH3 : (1 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 1000000001) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 1000000000) ” 
  &&  “ ((GcdValue (a_pre) (b_pre)) = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
.

Definition gcdll_entail_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000001)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  TT && emp 
|--
  “ (1 <= b) ” 
  &&  “ (b <= 1000000001) ” 
  &&  “ (0 <= (a % ( b ) )) ” 
  &&  “ ((a % ( b ) ) <= 1000000000) ” 
  &&  “ ((GcdValue (b) ((a % ( b ) ))) = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000001)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  TT && emp 
|--
  “ ((GcdValue (b) ((a % ( b ) ))) = (GcdValue (a_pre) (b_pre))) ” 
  &&  “ ((a % ( b ) ) <= 1000000000) ” 
  &&  “ (0 <= (a % ( b ) )) ”
  &&  emp
).

Definition gcdll_entail_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000001)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  ((GcdValue (b) ((a % ( b ) ))) = (GcdValue (a_pre) (b_pre)))
.

Definition gcdll_entail_wit_2_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000001)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  ((a % ( b ) ) <= 1000000000)
.

Definition gcdll_entail_wit_2_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000001)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  (0 <= (a % ( b ) ))
.

Definition gcdll_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000001)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b = 0)) ,
  TT && emp 
|--
  “ (a = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000001)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b = 0)) ,
  TT && emp 
|--
  “ (a = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
).

Definition gcdll_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000001)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b = 0)) ,
  (a = (GcdValue (a_pre) (b_pre)))
.

(*----- Function lcm_cap -----*)

Definition lcm_cap_safety_wit_1 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (1 <= cap_pre)) (PreH2 : (cap_pre <= 1000000000)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= (cap_pre + 1 ))) (PreH5 : (1 <= b_pre)) (PreH6 : (b_pre <= cap_pre)) (PreH7 : (g = (GcdValue (a_pre) (b_pre)))) (PreH8 : (1 <= g)) (PreH9 : (g <= b_pre)) ,
  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ ((cap_pre <> (INT64_MIN)) \/ (b_pre <> (-1))) ” 
  &&  “ (b_pre <> 0) ”
.

Definition lcm_cap_safety_wit_2 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (1 <= cap_pre)) (PreH2 : (cap_pre <= 1000000000)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= (cap_pre + 1 ))) (PreH5 : (1 <= b_pre)) (PreH6 : (b_pre <= cap_pre)) (PreH7 : (g = (GcdValue (a_pre) (b_pre)))) (PreH8 : (1 <= g)) (PreH9 : (g <= b_pre)) ,
  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ ((a_pre <> (INT64_MIN)) \/ (g <> (-1))) ” 
  &&  “ (g <> 0) ”
.

Definition lcm_cap_safety_wit_3 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : ((a_pre ÷ g ) > (cap_pre ÷ b_pre ))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) (PreH8 : (g = (GcdValue (a_pre) (b_pre)))) (PreH9 : (1 <= g)) (PreH10 : (g <= b_pre)) ,
  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ ((cap_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (cap_pre + 1 )) ”
.

Definition lcm_cap_safety_wit_4 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : ((a_pre ÷ g ) > (cap_pre ÷ b_pre ))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) (PreH8 : (g = (GcdValue (a_pre) (b_pre)))) (PreH9 : (1 <= g)) (PreH10 : (g <= b_pre)) ,
  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcm_cap_safety_wit_5 := 
(
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) (PreH8 : (g = (GcdValue (a_pre) (b_pre)))) (PreH9 : (1 <= g)) (PreH10 : (g <= b_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ (((a_pre ÷ g ) * b_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((a_pre ÷ g ) * b_pre )) ”
) \/
(
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) (PreH8 : (g = (GcdValue (a_pre) (b_pre)))) (PreH9 : (1 <= g)) (PreH10 : (g <= b_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ (((a_pre ÷ g ) * b_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((a_pre ÷ g ) * b_pre )) ”
).

Definition lcm_cap_safety_wit_5_split_goal_1 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) (PreH8 : (g = (GcdValue (a_pre) (b_pre)))) (PreH9 : (1 <= g)) (PreH10 : (g <= b_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ (((a_pre ÷ g ) * b_pre ) <= INT64_MAX) ”
.

Definition lcm_cap_safety_wit_5_split_goal_2 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) (PreH8 : (g = (GcdValue (a_pre) (b_pre)))) (PreH9 : (1 <= g)) (PreH10 : (g <= b_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ ((INT64_MIN) <= ((a_pre ÷ g ) * b_pre )) ”
.

Definition lcm_cap_safety_wit_6 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) (PreH8 : (g = (GcdValue (a_pre) (b_pre)))) (PreH9 : (1 <= g)) (PreH10 : (g <= b_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ ((a_pre <> (INT64_MIN)) \/ (g <> (-1))) ” 
  &&  “ (g <> 0) ”
.

Definition lcm_cap_safety_wit_7 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (((a_pre ÷ g ) * b_pre ) > cap_pre)) (PreH2 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH3 : (1 <= cap_pre)) (PreH4 : (cap_pre <= 1000000000)) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= (cap_pre + 1 ))) (PreH7 : (1 <= b_pre)) (PreH8 : (b_pre <= cap_pre)) (PreH9 : (g = (GcdValue (a_pre) (b_pre)))) (PreH10 : (1 <= g)) (PreH11 : (g <= b_pre)) ,
  ((( &( "x" ) )) # Int64  |-> ((a_pre ÷ g ) * b_pre ))
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ ((cap_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (cap_pre + 1 )) ”
.

Definition lcm_cap_safety_wit_8 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (((a_pre ÷ g ) * b_pre ) > cap_pre)) (PreH2 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH3 : (1 <= cap_pre)) (PreH4 : (cap_pre <= 1000000000)) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= (cap_pre + 1 ))) (PreH7 : (1 <= b_pre)) (PreH8 : (b_pre <= cap_pre)) (PreH9 : (g = (GcdValue (a_pre) (b_pre)))) (PreH10 : (1 <= g)) (PreH11 : (g <= b_pre)) ,
  ((( &( "x" ) )) # Int64  |-> ((a_pre ÷ g ) * b_pre ))
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
  **  ((( &( "g" ) )) # Int64  |-> g)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcm_cap_entail_wit_1 := 
(
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (a_pre) (b_pre)))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) ,
  TT && emp 
|--
  “ (1 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= (cap_pre + 1 )) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= cap_pre) ” 
  &&  “ (retval = (GcdValue (a_pre) (b_pre))) ” 
  &&  “ (1 <= retval) ” 
  &&  “ (retval <= b_pre) ”
  &&  emp
) \/
(
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (a_pre) (b_pre)))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) ,
  TT && emp 
|--
  “ (retval <= b_pre) ” 
  &&  “ (1 <= retval) ”
  &&  emp
).

Definition lcm_cap_entail_wit_1_split_goal_1 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (a_pre) (b_pre)))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) ,
  (retval <= b_pre)
.

Definition lcm_cap_entail_wit_1_split_goal_2 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (a_pre) (b_pre)))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) ,
  (1 <= retval)
.

Definition lcm_cap_return_wit_1 := 
(
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (((a_pre ÷ g ) * b_pre ) > cap_pre)) (PreH2 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH3 : (1 <= cap_pre)) (PreH4 : (cap_pre <= 1000000000)) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= (cap_pre + 1 ))) (PreH7 : (1 <= b_pre)) (PreH8 : (b_pre <= cap_pre)) (PreH9 : (g = (GcdValue (a_pre) (b_pre)))) (PreH10 : (1 <= g)) (PreH11 : (g <= b_pre)) ,
  TT && emp 
|--
  “ (1 <= (cap_pre + 1 )) ” 
  &&  “ ((cap_pre + 1 ) <= (cap_pre + 1 )) ” 
  &&  “ (LcmCapValue a_pre b_pre cap_pre (cap_pre + 1 ) ) ”
  &&  emp
) \/
(
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (((a_pre ÷ g ) * b_pre ) > cap_pre)) (PreH2 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH3 : (1 <= cap_pre)) (PreH4 : (cap_pre <= 1000000000)) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= (cap_pre + 1 ))) (PreH7 : (1 <= b_pre)) (PreH8 : (b_pre <= cap_pre)) (PreH9 : (g = (GcdValue (a_pre) (b_pre)))) (PreH10 : (1 <= g)) (PreH11 : (g <= b_pre)) ,
  TT && emp 
|--
  “ (LcmCapValue a_pre b_pre cap_pre (cap_pre + 1 ) ) ”
  &&  emp
).

Definition lcm_cap_return_wit_1_split_goal_1 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (((a_pre ÷ g ) * b_pre ) > cap_pre)) (PreH2 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH3 : (1 <= cap_pre)) (PreH4 : (cap_pre <= 1000000000)) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= (cap_pre + 1 ))) (PreH7 : (1 <= b_pre)) (PreH8 : (b_pre <= cap_pre)) (PreH9 : (g = (GcdValue (a_pre) (b_pre)))) (PreH10 : (1 <= g)) (PreH11 : (g <= b_pre)) ,
  (LcmCapValue a_pre b_pre cap_pre (cap_pre + 1 ) )
.

Definition lcm_cap_return_wit_2 := 
(
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (((a_pre ÷ g ) * b_pre ) <= cap_pre)) (PreH2 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH3 : (1 <= cap_pre)) (PreH4 : (cap_pre <= 1000000000)) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= (cap_pre + 1 ))) (PreH7 : (1 <= b_pre)) (PreH8 : (b_pre <= cap_pre)) (PreH9 : (g = (GcdValue (a_pre) (b_pre)))) (PreH10 : (1 <= g)) (PreH11 : (g <= b_pre)) ,
  TT && emp 
|--
  “ (1 <= ((a_pre ÷ g ) * b_pre )) ” 
  &&  “ (((a_pre ÷ g ) * b_pre ) <= (cap_pre + 1 )) ” 
  &&  “ (LcmCapValue a_pre b_pre cap_pre ((a_pre ÷ g ) * b_pre ) ) ”
  &&  emp
) \/
(
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (((a_pre ÷ g ) * b_pre ) <= cap_pre)) (PreH2 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH3 : (1 <= cap_pre)) (PreH4 : (cap_pre <= 1000000000)) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= (cap_pre + 1 ))) (PreH7 : (1 <= b_pre)) (PreH8 : (b_pre <= cap_pre)) (PreH9 : (g = (GcdValue (a_pre) (b_pre)))) (PreH10 : (1 <= g)) (PreH11 : (g <= b_pre)) ,
  TT && emp 
|--
  “ (LcmCapValue a_pre b_pre cap_pre ((a_pre ÷ g ) * b_pre ) ) ” 
  &&  “ (1 <= ((a_pre ÷ g ) * b_pre )) ”
  &&  emp
).

Definition lcm_cap_return_wit_2_split_goal_1 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (((a_pre ÷ g ) * b_pre ) <= cap_pre)) (PreH2 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH3 : (1 <= cap_pre)) (PreH4 : (cap_pre <= 1000000000)) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= (cap_pre + 1 ))) (PreH7 : (1 <= b_pre)) (PreH8 : (b_pre <= cap_pre)) (PreH9 : (g = (GcdValue (a_pre) (b_pre)))) (PreH10 : (1 <= g)) (PreH11 : (g <= b_pre)) ,
  (LcmCapValue a_pre b_pre cap_pre ((a_pre ÷ g ) * b_pre ) )
.

Definition lcm_cap_return_wit_2_split_goal_2 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : (((a_pre ÷ g ) * b_pre ) <= cap_pre)) (PreH2 : ((a_pre ÷ g ) <= (cap_pre ÷ b_pre ))) (PreH3 : (1 <= cap_pre)) (PreH4 : (cap_pre <= 1000000000)) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= (cap_pre + 1 ))) (PreH7 : (1 <= b_pre)) (PreH8 : (b_pre <= cap_pre)) (PreH9 : (g = (GcdValue (a_pre) (b_pre)))) (PreH10 : (1 <= g)) (PreH11 : (g <= b_pre)) ,
  (1 <= ((a_pre ÷ g ) * b_pre ))
.

Definition lcm_cap_return_wit_3 := 
(
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : ((a_pre ÷ g ) > (cap_pre ÷ b_pre ))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) (PreH8 : (g = (GcdValue (a_pre) (b_pre)))) (PreH9 : (1 <= g)) (PreH10 : (g <= b_pre)) ,
  TT && emp 
|--
  “ (1 <= (cap_pre + 1 )) ” 
  &&  “ ((cap_pre + 1 ) <= (cap_pre + 1 )) ” 
  &&  “ (LcmCapValue a_pre b_pre cap_pre (cap_pre + 1 ) ) ”
  &&  emp
) \/
(
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : ((a_pre ÷ g ) > (cap_pre ÷ b_pre ))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) (PreH8 : (g = (GcdValue (a_pre) (b_pre)))) (PreH9 : (1 <= g)) (PreH10 : (g <= b_pre)) ,
  TT && emp 
|--
  “ (LcmCapValue a_pre b_pre cap_pre (cap_pre + 1 ) ) ”
  &&  emp
).

Definition lcm_cap_return_wit_3_split_goal_1 := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (g: Z) (PreH1 : ((a_pre ÷ g ) > (cap_pre ÷ b_pre ))) (PreH2 : (1 <= cap_pre)) (PreH3 : (cap_pre <= 1000000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= (cap_pre + 1 ))) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= cap_pre)) (PreH8 : (g = (GcdValue (a_pre) (b_pre)))) (PreH9 : (1 <= g)) (PreH10 : (g <= b_pre)) ,
  (LcmCapValue a_pre b_pre cap_pre (cap_pre + 1 ) )
.

Definition lcm_cap_partial_solve_wit_1_pure := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (1 <= cap_pre)) (PreH2 : (cap_pre <= 1000000000)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= (cap_pre + 1 ))) (PreH5 : (1 <= b_pre)) (PreH6 : (b_pre <= cap_pre)) ,
  ((( &( "g" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "cap" ) )) # Int64  |-> cap_pre)
|--
  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 1000000001) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= 1000000000) ”
.

Definition lcm_cap_partial_solve_wit_1_aux := 
forall (cap_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (1 <= cap_pre)) (PreH2 : (cap_pre <= 1000000000)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= (cap_pre + 1 ))) (PreH5 : (1 <= b_pre)) (PreH6 : (b_pre <= cap_pre)) ,
  TT && emp 
|--
  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 1000000001) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= 1000000000) ” 
  &&  “ (1 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= (cap_pre + 1 )) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= cap_pre) ”
  &&  emp
.

Definition lcm_cap_partial_solve_wit_1 := lcm_cap_partial_solve_wit_1_pure -> lcm_cap_partial_solve_wit_1_aux.

(*----- Function cmp_int -----*)

Definition cmp_int_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx > vy)) ,
  ((( &( "b" ) )) # Int  |-> vy)
  **  ((( &( "a" ) )) # Int  |-> vx)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> vx)
  **  ((y_pre) # Int  |-> vy)
|--
  “ ((1 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 - 0 )) ”
.

Definition cmp_int_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx < vy)) (PreH2 : (vx <= vy)) ,
  ((( &( "b" ) )) # Int  |-> vy)
  **  ((( &( "a" ) )) # Int  |-> vx)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> vx)
  **  ((y_pre) # Int  |-> vy)
|--
  “ ((0 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 1 )) ”
.

Definition cmp_int_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx <= vy)) ,
  ((( &( "b" ) )) # Int  |-> vy)
  **  ((( &( "a" ) )) # Int  |-> vx)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> vx)
  **  ((y_pre) # Int  |-> vy)
|--
  “ ((0 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 0 )) ”
.

Definition cmp_int_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx < vy)) (PreH2 : (vx > vy)) ,
  ((( &( "b" ) )) # Int  |-> vy)
  **  ((( &( "a" ) )) # Int  |-> vx)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> vx)
  **  ((y_pre) # Int  |-> vy)
|--
  “ False ”
.

Definition cmp_int_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx <= vy)) ,
  ((x_pre) # Int  |-> vx)
  **  ((y_pre) # Int  |-> vy)
|--
  “ (CompareResult vx vy (0 - 0 ) ) ”
  &&  ((x_pre) # Int  |-> vx)
  **  ((y_pre) # Int  |-> vy)
) \/
(
forall (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx <= vy)) ,
  TT && emp 
|--
  “ (CompareResult vx vy (0 - 0 ) ) ”
  &&  emp
).

Definition cmp_int_return_wit_1_split_goal_1 := 
forall (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx <= vy)) ,
  (CompareResult vx vy (0 - 0 ) )
.

Definition cmp_int_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx < vy)) (PreH2 : (vx <= vy)) ,
  ((x_pre) # Int  |-> vx)
  **  ((y_pre) # Int  |-> vy)
|--
  “ (CompareResult vx vy (0 - 1 ) ) ”
  &&  ((x_pre) # Int  |-> vx)
  **  ((y_pre) # Int  |-> vy)
) \/
(
forall (vy: Z) (vx: Z) (PreH1 : (vx < vy)) (PreH2 : (vx <= vy)) ,
  TT && emp 
|--
  “ (CompareResult vx vy (0 - 1 ) ) ”
  &&  emp
).

Definition cmp_int_return_wit_2_split_goal_1 := 
forall (vy: Z) (vx: Z) (PreH1 : (vx < vy)) (PreH2 : (vx <= vy)) ,
  (CompareResult vx vy (0 - 1 ) )
.

Definition cmp_int_return_wit_3 := 
(
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx > vy)) ,
  ((x_pre) # Int  |-> vx)
  **  ((y_pre) # Int  |-> vy)
|--
  “ (CompareResult vx vy (1 - 0 ) ) ”
  &&  ((x_pre) # Int  |-> vx)
  **  ((y_pre) # Int  |-> vy)
) \/
(
forall (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx > vy)) ,
  TT && emp 
|--
  “ (CompareResult vx vy (1 - 0 ) ) ”
  &&  emp
).

Definition cmp_int_return_wit_3_split_goal_1 := 
forall (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx > vy)) ,
  (CompareResult vx vy (1 - 0 ) )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (PreH1 : (retval <> 0)) (PreH2 : (original = a)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "mx" ) )) # Int  |->_)
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> retval)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full input_pre n_pre original )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (PreH1 : (retval <> 0)) (PreH2 : (original = a)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "all" ) )) # Int64  |->_)
  **  ((( &( "mx" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> retval)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full input_pre n_pre original )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (PreH1 : (retval <> 0)) (PreH2 : (original = a)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "all" ) )) # Int64  |-> 1)
  **  ((( &( "mx" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> retval)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full input_pre n_pre original )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : ((Znth (i - 0 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) 0) > mx)) (PreH2 : (i < n_pre)) (PreH3 : (a_2 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= mx)) (PreH11 : (mx <= 1000000000)) (PreH12 : (CopyMaxState original copied i mx )) (PreH13 : (retval <> 0)) (PreH14 : (original = a)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.seg a_2 0 (i + 1 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
  **  (IntArray.full input_pre n_pre original )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mx" ) )) # Int  |-> (Znth (i - 0 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) 0))
  **  ((( &( "all" ) )) # Int64  |-> 1)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : ((Znth (i - 0 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) 0) <= mx)) (PreH2 : (i < n_pre)) (PreH3 : (a_2 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= mx)) (PreH11 : (mx <= 1000000000)) (PreH12 : (CopyMaxState original copied i mx )) (PreH13 : (retval <> 0)) (PreH14 : (original = a)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.seg a_2 0 (i + 1 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
  **  (IntArray.full input_pre n_pre original )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "all" ) )) # Int64  |-> 1)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_2)
  **  (IntArray.full a_2 n_pre copied )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  (IntArray.full input_pre n_pre original )
  **  ((( &( "all" ) )) # Int64  |-> 1)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (mx_2 + 1 ))) (PreH3 : (LcmCapValue all (Znth i copied 0) mx_2 retval_2 )) (PreH4 : (i < n_pre)) (PreH5 : (a_3 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH12 : (1 <= mx_2)) (PreH13 : (mx_2 <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (1 <= all)) (PreH17 : (all <= (mx_2 + 1 ))) (PreH18 : (CopyMaxState original copied n_pre mx_2 )) (PreH19 : (LcmPrefixState copied i mx_2 all )) (PreH20 : (finished_i >= n_pre)) (PreH21 : (a_2 <> 0)) (PreH22 : (n_pre = (Zlength (original)))) (PreH23 : (1 <= n_pre)) (PreH24 : (n_pre <= 2000)) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH26 : (0 <= finished_i)) (PreH27 : (finished_i <= n_pre)) (PreH28 : (0 <= mx)) (PreH29 : (mx <= 1000000000)) (PreH30 : (CopyMaxState original copied finished_i mx )) (PreH31 : (retval <> 0)) (PreH32 : (original = a)) (PreH33 : (n_pre = (Zlength (original)))) (PreH34 : (1 <= n_pre)) (PreH35 : (n_pre <= 2000)) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_3 n_pre copied )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_3)
  **  ((( &( "mx" ) )) # Int  |-> mx_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "all" ) )) # Int64  |-> retval_2)
  **  (IntArray.full input_pre n_pre original )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (a_3 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : (1 <= all)) (PreH8 : (all <= 1000000000)) (PreH9 : (all = all)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH12 : (CopyMaxState original copied n_pre all )) (PreH13 : (LcmPrefixState copied n_pre all all )) (PreH14 : (Permutation copied sorted )) (PreH15 : (Permutation copied sorted )) (PreH16 : ((Zlength (sorted)) = n_pre)) (PreH17 : (all = mx_2)) (PreH18 : (i >= n_pre)) (PreH19 : (a_3 <> 0)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : ((Zlength (copied)) = n_pre)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 2000)) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH26 : (1 <= mx_2)) (PreH27 : (mx_2 <= 1000000000)) (PreH28 : (0 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= all)) (PreH31 : (all <= (mx_2 + 1 ))) (PreH32 : (CopyMaxState original copied n_pre mx_2 )) (PreH33 : (LcmPrefixState copied i mx_2 all )) (PreH34 : (finished_i >= n_pre)) (PreH35 : (a_2 <> 0)) (PreH36 : (n_pre = (Zlength (original)))) (PreH37 : (1 <= n_pre)) (PreH38 : (n_pre <= 2000)) (PreH39 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH40 : (0 <= finished_i)) (PreH41 : (finished_i <= n_pre)) (PreH42 : (0 <= mx)) (PreH43 : (mx <= 1000000000)) (PreH44 : (CopyMaxState original copied finished_i mx )) (PreH45 : (retval <> 0)) (PreH46 : (original = a)) (PreH47 : (n_pre = (Zlength (original)))) (PreH48 : (1 <= n_pre)) (PreH49 : (n_pre <= 2000)) (PreH50 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_3)
  **  ((( &( "mx" ) )) # Int  |-> all)
  **  ((( &( "all" ) )) # Int64  |-> all)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre sorted )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (a_3 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : (1 <= all)) (PreH8 : (all <= 1000000000)) (PreH9 : (all = all)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH12 : (CopyMaxState original copied n_pre all )) (PreH13 : (LcmPrefixState copied n_pre all all )) (PreH14 : (Permutation copied sorted )) (PreH15 : (Permutation copied sorted )) (PreH16 : ((Zlength (sorted)) = n_pre)) (PreH17 : (all = mx_2)) (PreH18 : (i >= n_pre)) (PreH19 : (a_3 <> 0)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : ((Zlength (copied)) = n_pre)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 2000)) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH26 : (1 <= mx_2)) (PreH27 : (mx_2 <= 1000000000)) (PreH28 : (0 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= all)) (PreH31 : (all <= (mx_2 + 1 ))) (PreH32 : (CopyMaxState original copied n_pre mx_2 )) (PreH33 : (LcmPrefixState copied i mx_2 all )) (PreH34 : (finished_i >= n_pre)) (PreH35 : (a_2 <> 0)) (PreH36 : (n_pre = (Zlength (original)))) (PreH37 : (1 <= n_pre)) (PreH38 : (n_pre <= 2000)) (PreH39 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH40 : (0 <= finished_i)) (PreH41 : (finished_i <= n_pre)) (PreH42 : (0 <= mx)) (PreH43 : (mx <= 1000000000)) (PreH44 : (CopyMaxState original copied finished_i mx )) (PreH45 : (retval <> 0)) (PreH46 : (original = a)) (PreH47 : (n_pre = (Zlength (original)))) (PreH48 : (1 <= n_pre)) (PreH49 : (n_pre <= 2000)) (PreH50 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_3)
  **  ((( &( "mx" ) )) # Int  |-> all)
  **  ((( &( "all" ) )) # Int64  |-> all)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre sorted )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : (a_4 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : (1 <= mx_3)) (PreH8 : (mx_3 <= 1000000000)) (PreH9 : (all_2 = mx_3)) (PreH10 : (1 <= q)) (PreH11 : (q <= 31624)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= n_pre)) (PreH14 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH15 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH16 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH17 : (CopyMaxState original copied n_pre mx_3 )) (PreH18 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH19 : (Permutation copied sorted )) (PreH20 : (DivisorBestState original mx_3 q 0 ans )) (PreH21 : (a_3 <> 0)) (PreH22 : (n_pre = (Zlength (original)))) (PreH23 : ((Zlength (copied)) = n_pre)) (PreH24 : ((Zlength (sorted)) = n_pre)) (PreH25 : (1 <= n_pre)) (PreH26 : (n_pre <= 2000)) (PreH27 : (1 <= all)) (PreH28 : (all <= 1000000000)) (PreH29 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH30 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH31 : (CopyMaxState original copied n_pre all )) (PreH32 : (LcmPrefixState copied n_pre all all )) (PreH33 : (Permutation copied sorted )) (PreH34 : (Permutation copied sorted )) (PreH35 : ((Zlength (sorted)) = n_pre)) (PreH36 : (all = mx_2)) (PreH37 : (i >= n_pre)) (PreH38 : (a_3 <> 0)) (PreH39 : (n_pre = (Zlength (original)))) (PreH40 : ((Zlength (copied)) = n_pre)) (PreH41 : (1 <= n_pre)) (PreH42 : (n_pre <= 2000)) (PreH43 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH44 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH45 : (1 <= mx_2)) (PreH46 : (mx_2 <= 1000000000)) (PreH47 : (0 <= i)) (PreH48 : (i <= n_pre)) (PreH49 : (1 <= all)) (PreH50 : (all <= (mx_2 + 1 ))) (PreH51 : (CopyMaxState original copied n_pre mx_2 )) (PreH52 : (LcmPrefixState copied i mx_2 all )) (PreH53 : (finished_i >= n_pre)) (PreH54 : (a_2 <> 0)) (PreH55 : (n_pre = (Zlength (original)))) (PreH56 : (1 <= n_pre)) (PreH57 : (n_pre <= 2000)) (PreH58 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH59 : (0 <= finished_i)) (PreH60 : (finished_i <= n_pre)) (PreH61 : (0 <= mx)) (PreH62 : (mx <= 1000000000)) (PreH63 : (CopyMaxState original copied finished_i mx )) (PreH64 : (retval <> 0)) (PreH65 : (original = a)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_4)
  **  ((( &( "mx" ) )) # Int  |-> mx_3)
  **  ((( &( "all" ) )) # Int64  |-> all_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ ((q * q ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (q * q )) ”
.

Definition solver_safety_wit_11 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx_2: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_3: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx: Z) (a_4: Z) (PreH1 : ((q * q ) <= mx)) (PreH2 : (a_4 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx)) (PreH9 : (mx <= 1000000000)) (PreH10 : (all_2 = mx)) (PreH11 : (1 <= q)) (PreH12 : (q <= 31624)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= n_pre)) (PreH15 : (((q - 1 ) * (q - 1 ) ) <= mx)) (PreH16 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH18 : (CopyMaxState original copied n_pre mx )) (PreH19 : (LcmPrefixState copied n_pre mx all_2 )) (PreH20 : (Permutation copied sorted )) (PreH21 : (DivisorBestState original mx q 0 ans )) (PreH22 : (a_3 <> 0)) (PreH23 : (n_pre = (Zlength (original)))) (PreH24 : ((Zlength (copied)) = n_pre)) (PreH25 : ((Zlength (sorted)) = n_pre)) (PreH26 : (1 <= n_pre)) (PreH27 : (n_pre <= 2000)) (PreH28 : (1 <= all)) (PreH29 : (all <= 1000000000)) (PreH30 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH31 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH32 : (CopyMaxState original copied n_pre all )) (PreH33 : (LcmPrefixState copied n_pre all all )) (PreH34 : (Permutation copied sorted )) (PreH35 : (Permutation copied sorted )) (PreH36 : ((Zlength (sorted)) = n_pre)) (PreH37 : (all = mx_3)) (PreH38 : (i >= n_pre)) (PreH39 : (a_3 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : (1 <= n_pre)) (PreH43 : (n_pre <= 2000)) (PreH44 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH45 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH46 : (1 <= mx_3)) (PreH47 : (mx_3 <= 1000000000)) (PreH48 : (0 <= i)) (PreH49 : (i <= n_pre)) (PreH50 : (1 <= all)) (PreH51 : (all <= (mx_3 + 1 ))) (PreH52 : (CopyMaxState original copied n_pre mx_3 )) (PreH53 : (LcmPrefixState copied i mx_3 all )) (PreH54 : (finished_i >= n_pre)) (PreH55 : (a_2 <> 0)) (PreH56 : (n_pre = (Zlength (original)))) (PreH57 : (1 <= n_pre)) (PreH58 : (n_pre <= 2000)) (PreH59 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH60 : (0 <= finished_i)) (PreH61 : (finished_i <= n_pre)) (PreH62 : (0 <= mx_2)) (PreH63 : (mx_2 <= 1000000000)) (PreH64 : (CopyMaxState original copied finished_i mx_2 )) (PreH65 : (retval <> 0)) (PreH66 : (original = a)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_4)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "all" ) )) # Int64  |-> all_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ ((mx <> (INT_MIN)) \/ (q <> (-1))) ” 
  &&  “ (q <> 0) ”
.

Definition solver_safety_wit_12 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((q * q ) <= mx_3)) (PreH2 : (a_4 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_3)) (PreH9 : (mx_3 <= 1000000000)) (PreH10 : (all_2 = mx_3)) (PreH11 : (1 <= q)) (PreH12 : (q <= 31624)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= n_pre)) (PreH15 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH16 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH18 : (CopyMaxState original copied n_pre mx_3 )) (PreH19 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH20 : (Permutation copied sorted )) (PreH21 : (DivisorBestState original mx_3 q 0 ans )) (PreH22 : (a_3 <> 0)) (PreH23 : (n_pre = (Zlength (original)))) (PreH24 : ((Zlength (copied)) = n_pre)) (PreH25 : ((Zlength (sorted)) = n_pre)) (PreH26 : (1 <= n_pre)) (PreH27 : (n_pre <= 2000)) (PreH28 : (1 <= all)) (PreH29 : (all <= 1000000000)) (PreH30 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH31 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH32 : (CopyMaxState original copied n_pre all )) (PreH33 : (LcmPrefixState copied n_pre all all )) (PreH34 : (Permutation copied sorted )) (PreH35 : (Permutation copied sorted )) (PreH36 : ((Zlength (sorted)) = n_pre)) (PreH37 : (all = mx_2)) (PreH38 : (i >= n_pre)) (PreH39 : (a_3 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : (1 <= n_pre)) (PreH43 : (n_pre <= 2000)) (PreH44 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH45 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH46 : (1 <= mx_2)) (PreH47 : (mx_2 <= 1000000000)) (PreH48 : (0 <= i)) (PreH49 : (i <= n_pre)) (PreH50 : (1 <= all)) (PreH51 : (all <= (mx_2 + 1 ))) (PreH52 : (CopyMaxState original copied n_pre mx_2 )) (PreH53 : (LcmPrefixState copied i mx_2 all )) (PreH54 : (finished_i >= n_pre)) (PreH55 : (a_2 <> 0)) (PreH56 : (n_pre = (Zlength (original)))) (PreH57 : (1 <= n_pre)) (PreH58 : (n_pre <= 2000)) (PreH59 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH60 : (0 <= finished_i)) (PreH61 : (finished_i <= n_pre)) (PreH62 : (0 <= mx)) (PreH63 : (mx <= 1000000000)) (PreH64 : (CopyMaxState original copied finished_i mx )) (PreH65 : (retval <> 0)) (PreH66 : (original = a)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_4)
  **  ((( &( "mx" ) )) # Int  |-> mx_3)
  **  ((( &( "all" ) )) # Int64  |-> all_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx_2: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_3: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx: Z) (a_4: Z) (PreH1 : ((mx % ( q ) ) = 0)) (PreH2 : ((q * q ) <= mx)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (all_2 = mx)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx )) (PreH20 : (LcmPrefixState copied n_pre mx all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_3)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_3)) (PreH48 : (mx_3 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_3 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_3 )) (PreH54 : (LcmPrefixState copied i mx_3 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx_2)) (PreH64 : (mx_2 <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx_2 )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_4)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "all" ) )) # Int64  |-> all_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ ((mx <> (INT_MIN)) \/ (q <> (-1))) ” 
  &&  “ (q <> 0) ”
.

Definition solver_safety_wit_14 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((mx_3 % ( q ) ) = 0)) (PreH2 : ((q * q ) <= mx_3)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_3)) (PreH10 : (mx_3 <= 1000000000)) (PreH11 : (all_2 = mx_3)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx_3 )) (PreH20 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx_3 q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_2)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_2)) (PreH48 : (mx_2 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_2 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_2 )) (PreH54 : (LcmPrefixState copied i mx_2 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx)) (PreH64 : (mx <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "z" ) )) # Int  |->_)
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q) ((cons ((mx_3 ÷ q )) ((@nil Z))))) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_4)
  **  ((( &( "mx" ) )) # Int  |-> mx_3)
  **  ((( &( "all" ) )) # Int64  |-> all_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (a_5 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : (1 <= mx_4)) (PreH8 : (mx_4 <= 1000000000)) (PreH9 : (all_3 = mx_4)) (PreH10 : (1 <= q_2)) (PreH11 : (q_2 <= 31623)) (PreH12 : ((q_2 * q_2 ) <= mx_4)) (PreH13 : ((mx_4 % ( q_2 ) ) = 0)) (PreH14 : (0 <= z)) (PreH15 : (z <= 2)) (PreH16 : (0 <= ans_2)) (PreH17 : (ans_2 <= n_pre)) (PreH18 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH19 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH20 : (CopyMaxState original copied n_pre mx_4 )) (PreH21 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH22 : (Permutation copied sorted )) (PreH23 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH24 : ((mx_3 % ( q ) ) = 0)) (PreH25 : ((q * q ) <= mx_3)) (PreH26 : (a_4 <> 0)) (PreH27 : (n_pre = (Zlength (original)))) (PreH28 : ((Zlength (copied)) = n_pre)) (PreH29 : ((Zlength (sorted)) = n_pre)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 2000)) (PreH32 : (1 <= mx_3)) (PreH33 : (mx_3 <= 1000000000)) (PreH34 : (all_2 = mx_3)) (PreH35 : (1 <= q)) (PreH36 : (q <= 31624)) (PreH37 : (0 <= ans)) (PreH38 : (ans <= n_pre)) (PreH39 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH40 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH41 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH42 : (CopyMaxState original copied n_pre mx_3 )) (PreH43 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH44 : (Permutation copied sorted )) (PreH45 : (DivisorBestState original mx_3 q 0 ans )) (PreH46 : (a_3 <> 0)) (PreH47 : (n_pre = (Zlength (original)))) (PreH48 : ((Zlength (copied)) = n_pre)) (PreH49 : ((Zlength (sorted)) = n_pre)) (PreH50 : (1 <= n_pre)) (PreH51 : (n_pre <= 2000)) (PreH52 : (1 <= all)) (PreH53 : (all <= 1000000000)) (PreH54 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH55 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH56 : (CopyMaxState original copied n_pre all )) (PreH57 : (LcmPrefixState copied n_pre all all )) (PreH58 : (Permutation copied sorted )) (PreH59 : (Permutation copied sorted )) (PreH60 : ((Zlength (sorted)) = n_pre)) (PreH61 : (all = mx_2)) (PreH62 : (i >= n_pre)) (PreH63 : (a_3 <> 0)) (PreH64 : (n_pre = (Zlength (original)))) (PreH65 : ((Zlength (copied)) = n_pre)) (PreH66 : (1 <= n_pre)) (PreH67 : (n_pre <= 2000)) (PreH68 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH69 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH70 : (1 <= mx_2)) (PreH71 : (mx_2 <= 1000000000)) (PreH72 : (0 <= i)) (PreH73 : (i <= n_pre)) (PreH74 : (1 <= all)) (PreH75 : (all <= (mx_2 + 1 ))) (PreH76 : (CopyMaxState original copied n_pre mx_2 )) (PreH77 : (LcmPrefixState copied i mx_2 all )) (PreH78 : (finished_i >= n_pre)) (PreH79 : (a_2 <> 0)) (PreH80 : (n_pre = (Zlength (original)))) (PreH81 : (1 <= n_pre)) (PreH82 : (n_pre <= 2000)) (PreH83 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH84 : (0 <= finished_i)) (PreH85 : (finished_i <= n_pre)) (PreH86 : (0 <= mx)) (PreH87 : (mx <= 1000000000)) (PreH88 : (CopyMaxState original copied finished_i mx )) (PreH89 : (retval <> 0)) (PreH90 : (original = a)) (PreH91 : (n_pre = (Zlength (original)))) (PreH92 : (1 <= n_pre)) (PreH93 : (n_pre <= 2000)) (PreH94 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_5)
  **  ((( &( "mx" ) )) # Int  |-> mx_4)
  **  ((( &( "all" ) )) # Int64  |-> all_3)
  **  ((( &( "q" ) )) # Int  |-> q_2)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ans" ) )) # Int  |-> ans_2)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_16 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "present" ) )) # Int  |-> 0)
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_5)
  **  ((( &( "mx" ) )) # Int  |-> mx_4)
  **  ((( &( "all" ) )) # Int64  |-> all_3)
  **  ((( &( "q" ) )) # Int  |-> q_2)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ans" ) )) # Int  |-> ans_2)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "present" ) )) # Int  |->_)
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_5)
  **  ((( &( "mx" ) )) # Int  |-> mx_4)
  **  ((( &( "all" ) )) # Int64  |-> all_3)
  **  ((( &( "q" ) )) # Int  |-> q_2)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ans" ) )) # Int  |-> ans_2)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "l" ) )) # Int64  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "present" ) )) # Int  |-> 0)
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_5)
  **  ((( &( "mx" ) )) # Int  |-> mx_4)
  **  ((( &( "all" ) )) # Int64  |-> all_3)
  **  ((( &( "q" ) )) # Int  |-> q_2)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ans" ) )) # Int  |-> ans_2)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "l" ) )) # Int64  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "present" ) )) # Int  |-> 0)
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_5)
  **  ((( &( "mx" ) )) # Int  |-> mx_4)
  **  ((( &( "all" ) )) # Int64  |-> all_3)
  **  ((( &( "q" ) )) # Int  |-> q_2)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ans" ) )) # Int  |-> ans_2)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_20 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((Znth i_2 sorted 0) = d)) (PreH2 : (i_2 < n_pre)) (PreH3 : (a_6 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_5)) (PreH10 : (mx_5 <= 1000000000)) (PreH11 : (all_4 = mx_5)) (PreH12 : (1 <= q_3)) (PreH13 : (q_3 <= 31623)) (PreH14 : ((q_3 * q_3 ) <= mx_5)) (PreH15 : ((mx_5 % ( q_3 ) ) = 0)) (PreH16 : (0 <= z_2)) (PreH17 : (z_2 < 2)) (PreH18 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_5)) (PreH21 : (0 <= ans_3)) (PreH22 : (ans_3 <= n_pre)) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i_2)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_5 )) (PreH34 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH37 : (DivisorScanState sorted d i_2 present count l )) (PreH38 : (z < 2)) (PreH39 : (a_5 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_4)) (PreH46 : (mx_4 <= 1000000000)) (PreH47 : (all_3 = mx_4)) (PreH48 : (1 <= q_2)) (PreH49 : (q_2 <= 31623)) (PreH50 : ((q_2 * q_2 ) <= mx_4)) (PreH51 : ((mx_4 % ( q_2 ) ) = 0)) (PreH52 : (0 <= z)) (PreH53 : (z <= 2)) (PreH54 : (0 <= ans_2)) (PreH55 : (ans_2 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_4 )) (PreH59 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i)) (PreH111 : (i <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "present" ) )) # Int  |-> present)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((Znth i sorted 0) <> d)) (PreH2 : (i < n_pre)) (PreH3 : (a_6 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_5)) (PreH10 : (mx_5 <= 1000000000)) (PreH11 : (all_4 = mx_5)) (PreH12 : (1 <= q_3)) (PreH13 : (q_3 <= 31623)) (PreH14 : ((q_3 * q_3 ) <= mx_5)) (PreH15 : ((mx_5 % ( q_3 ) ) = 0)) (PreH16 : (0 <= z_2)) (PreH17 : (z_2 < 2)) (PreH18 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_5)) (PreH21 : (0 <= ans_3)) (PreH22 : (ans_3 <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_5 )) (PreH34 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH37 : (DivisorScanState sorted d i present count l )) (PreH38 : (z < 2)) (PreH39 : (a_5 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_4)) (PreH46 : (mx_4 <= 1000000000)) (PreH47 : (all_3 = mx_4)) (PreH48 : (1 <= q_2)) (PreH49 : (q_2 <= 31623)) (PreH50 : ((q_2 * q_2 ) <= mx_4)) (PreH51 : ((mx_4 % ( q_2 ) ) = 0)) (PreH52 : (0 <= z)) (PreH53 : (z <= 2)) (PreH54 : (0 <= ans_2)) (PreH55 : (ans_2 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_4 )) (PreH59 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i_2 >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i_2)) (PreH111 : (i_2 <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i_2 mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "present" ) )) # Int  |-> present)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((d <> (INT_MIN)) \/ ((Znth i sorted 0) <> (-1))) ” 
  &&  “ ((Znth i sorted 0) <> 0) ”
.

Definition solver_safety_wit_22 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((Znth i sorted 0) = d)) (PreH2 : (i < n_pre)) (PreH3 : (a_6 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_5)) (PreH10 : (mx_5 <= 1000000000)) (PreH11 : (all_4 = mx_5)) (PreH12 : (1 <= q_3)) (PreH13 : (q_3 <= 31623)) (PreH14 : ((q_3 * q_3 ) <= mx_5)) (PreH15 : ((mx_5 % ( q_3 ) ) = 0)) (PreH16 : (0 <= z_2)) (PreH17 : (z_2 < 2)) (PreH18 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_5)) (PreH21 : (0 <= ans_3)) (PreH22 : (ans_3 <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_5 )) (PreH34 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH37 : (DivisorScanState sorted d i present count l )) (PreH38 : (z < 2)) (PreH39 : (a_5 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_4)) (PreH46 : (mx_4 <= 1000000000)) (PreH47 : (all_3 = mx_4)) (PreH48 : (1 <= q_2)) (PreH49 : (q_2 <= 31623)) (PreH50 : ((q_2 * q_2 ) <= mx_4)) (PreH51 : ((mx_4 % ( q_2 ) ) = 0)) (PreH52 : (0 <= z)) (PreH53 : (z <= 2)) (PreH54 : (0 <= ans_2)) (PreH55 : (ans_2 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_4 )) (PreH59 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i_2 >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i_2)) (PreH111 : (i_2 <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i_2 mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "present" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((d <> (INT_MIN)) \/ ((Znth i sorted 0) <> (-1))) ” 
  &&  “ ((Znth i sorted 0) <> 0) ”
.

Definition solver_safety_wit_23 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((Znth i_2 sorted 0) = d)) (PreH2 : (i_2 < n_pre)) (PreH3 : (a_6 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_5)) (PreH10 : (mx_5 <= 1000000000)) (PreH11 : (all_4 = mx_5)) (PreH12 : (1 <= q_3)) (PreH13 : (q_3 <= 31623)) (PreH14 : ((q_3 * q_3 ) <= mx_5)) (PreH15 : ((mx_5 % ( q_3 ) ) = 0)) (PreH16 : (0 <= z_2)) (PreH17 : (z_2 < 2)) (PreH18 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_5)) (PreH21 : (0 <= ans_3)) (PreH22 : (ans_3 <= n_pre)) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i_2)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_5 )) (PreH34 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH37 : (DivisorScanState sorted d i_2 present count l )) (PreH38 : (z < 2)) (PreH39 : (a_5 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_4)) (PreH46 : (mx_4 <= 1000000000)) (PreH47 : (all_3 = mx_4)) (PreH48 : (1 <= q_2)) (PreH49 : (q_2 <= 31623)) (PreH50 : ((q_2 * q_2 ) <= mx_4)) (PreH51 : ((mx_4 % ( q_2 ) ) = 0)) (PreH52 : (0 <= z)) (PreH53 : (z <= 2)) (PreH54 : (0 <= ans_2)) (PreH55 : (ans_2 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_4 )) (PreH59 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i)) (PreH111 : (i <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "present" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((Znth i_2 sorted 0) <> d)) (PreH2 : (i_2 < n_pre)) (PreH3 : (a_6 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_5)) (PreH10 : (mx_5 <= 1000000000)) (PreH11 : (all_4 = mx_5)) (PreH12 : (1 <= q_3)) (PreH13 : (q_3 <= 31623)) (PreH14 : ((q_3 * q_3 ) <= mx_5)) (PreH15 : ((mx_5 % ( q_3 ) ) = 0)) (PreH16 : (0 <= z_2)) (PreH17 : (z_2 < 2)) (PreH18 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_5)) (PreH21 : (0 <= ans_3)) (PreH22 : (ans_3 <= n_pre)) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i_2)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_5 )) (PreH34 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH37 : (DivisorScanState sorted d i_2 present count l )) (PreH38 : (z < 2)) (PreH39 : (a_5 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_4)) (PreH46 : (mx_4 <= 1000000000)) (PreH47 : (all_3 = mx_4)) (PreH48 : (1 <= q_2)) (PreH49 : (q_2 <= 31623)) (PreH50 : ((q_2 * q_2 ) <= mx_4)) (PreH51 : ((mx_4 % ( q_2 ) ) = 0)) (PreH52 : (0 <= z)) (PreH53 : (z <= 2)) (PreH54 : (0 <= ans_2)) (PreH55 : (ans_2 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_4 )) (PreH59 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i)) (PreH111 : (i <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "present" ) )) # Int  |-> present)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_25 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i_2 sorted 0) ) ) = 0)) (PreH2 : ((Znth i_2 sorted 0) = d)) (PreH3 : (i_2 < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "present" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_26 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i_2 sorted 0) ) ) = 0)) (PreH2 : ((Znth i_2 sorted 0) <> d)) (PreH3 : (i_2 < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "present" ) )) # Int  |-> present)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_27 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (d + 1 ))) (PreH3 : (LcmCapValue l (Znth i sorted 0) d retval_2 )) (PreH4 : ((d % ( (Znth i sorted 0) ) ) = 0)) (PreH5 : ((Znth i sorted 0) = d)) (PreH6 : (i < n_pre)) (PreH7 : (a_6 <> 0)) (PreH8 : (n_pre = (Zlength (original)))) (PreH9 : ((Zlength (copied)) = n_pre)) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2000)) (PreH13 : (1 <= mx_5)) (PreH14 : (mx_5 <= 1000000000)) (PreH15 : (all_4 = mx_5)) (PreH16 : (1 <= q_3)) (PreH17 : (q_3 <= 31623)) (PreH18 : ((q_3 * q_3 ) <= mx_5)) (PreH19 : ((mx_5 % ( q_3 ) ) = 0)) (PreH20 : (0 <= z_2)) (PreH21 : (z_2 < 2)) (PreH22 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH23 : (1 <= d)) (PreH24 : (d <= mx_5)) (PreH25 : (0 <= ans_3)) (PreH26 : (ans_3 <= n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= present)) (PreH30 : (present <= 1)) (PreH31 : (0 <= count)) (PreH32 : (count <= i)) (PreH33 : (1 <= l)) (PreH34 : (l <= (d + 1 ))) (PreH35 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH36 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH37 : (CopyMaxState original copied n_pre mx_5 )) (PreH38 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH39 : (Permutation copied sorted )) (PreH40 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH41 : (DivisorScanState sorted d i present count l )) (PreH42 : (z < 2)) (PreH43 : (a_5 <> 0)) (PreH44 : (n_pre = (Zlength (original)))) (PreH45 : ((Zlength (copied)) = n_pre)) (PreH46 : ((Zlength (sorted)) = n_pre)) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : (1 <= mx_4)) (PreH50 : (mx_4 <= 1000000000)) (PreH51 : (all_3 = mx_4)) (PreH52 : (1 <= q_2)) (PreH53 : (q_2 <= 31623)) (PreH54 : ((q_2 * q_2 ) <= mx_4)) (PreH55 : ((mx_4 % ( q_2 ) ) = 0)) (PreH56 : (0 <= z)) (PreH57 : (z <= 2)) (PreH58 : (0 <= ans_2)) (PreH59 : (ans_2 <= n_pre)) (PreH60 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH61 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH62 : (CopyMaxState original copied n_pre mx_4 )) (PreH63 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH64 : (Permutation copied sorted )) (PreH65 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH66 : ((mx_3 % ( q ) ) = 0)) (PreH67 : ((q * q ) <= mx_3)) (PreH68 : (a_4 <> 0)) (PreH69 : (n_pre = (Zlength (original)))) (PreH70 : ((Zlength (copied)) = n_pre)) (PreH71 : ((Zlength (sorted)) = n_pre)) (PreH72 : (1 <= n_pre)) (PreH73 : (n_pre <= 2000)) (PreH74 : (1 <= mx_3)) (PreH75 : (mx_3 <= 1000000000)) (PreH76 : (all_2 = mx_3)) (PreH77 : (1 <= q)) (PreH78 : (q <= 31624)) (PreH79 : (0 <= ans)) (PreH80 : (ans <= n_pre)) (PreH81 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH82 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH83 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH84 : (CopyMaxState original copied n_pre mx_3 )) (PreH85 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH86 : (Permutation copied sorted )) (PreH87 : (DivisorBestState original mx_3 q 0 ans )) (PreH88 : (a_3 <> 0)) (PreH89 : (n_pre = (Zlength (original)))) (PreH90 : ((Zlength (copied)) = n_pre)) (PreH91 : ((Zlength (sorted)) = n_pre)) (PreH92 : (1 <= n_pre)) (PreH93 : (n_pre <= 2000)) (PreH94 : (1 <= all)) (PreH95 : (all <= 1000000000)) (PreH96 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH97 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH98 : (CopyMaxState original copied n_pre all )) (PreH99 : (LcmPrefixState copied n_pre all all )) (PreH100 : (Permutation copied sorted )) (PreH101 : (Permutation copied sorted )) (PreH102 : ((Zlength (sorted)) = n_pre)) (PreH103 : (all = mx_2)) (PreH104 : (i_2 >= n_pre)) (PreH105 : (a_3 <> 0)) (PreH106 : (n_pre = (Zlength (original)))) (PreH107 : ((Zlength (copied)) = n_pre)) (PreH108 : (1 <= n_pre)) (PreH109 : (n_pre <= 2000)) (PreH110 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH111 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH112 : (1 <= mx_2)) (PreH113 : (mx_2 <= 1000000000)) (PreH114 : (0 <= i_2)) (PreH115 : (i_2 <= n_pre)) (PreH116 : (1 <= all)) (PreH117 : (all <= (mx_2 + 1 ))) (PreH118 : (CopyMaxState original copied n_pre mx_2 )) (PreH119 : (LcmPrefixState copied i_2 mx_2 all )) (PreH120 : (finished_i >= n_pre)) (PreH121 : (a_2 <> 0)) (PreH122 : (n_pre = (Zlength (original)))) (PreH123 : (1 <= n_pre)) (PreH124 : (n_pre <= 2000)) (PreH125 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH126 : (0 <= finished_i)) (PreH127 : (finished_i <= n_pre)) (PreH128 : (0 <= mx)) (PreH129 : (mx <= 1000000000)) (PreH130 : (CopyMaxState original copied finished_i mx )) (PreH131 : (retval <> 0)) (PreH132 : (original = a)) (PreH133 : (n_pre = (Zlength (original)))) (PreH134 : (1 <= n_pre)) (PreH135 : (n_pre <= 2000)) (PreH136 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "present" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "l" ) )) # Int64  |-> retval_2)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_28 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (d + 1 ))) (PreH3 : (LcmCapValue l (Znth i sorted 0) d retval_2 )) (PreH4 : ((d % ( (Znth i sorted 0) ) ) = 0)) (PreH5 : ((Znth i sorted 0) <> d)) (PreH6 : (i < n_pre)) (PreH7 : (a_6 <> 0)) (PreH8 : (n_pre = (Zlength (original)))) (PreH9 : ((Zlength (copied)) = n_pre)) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2000)) (PreH13 : (1 <= mx_5)) (PreH14 : (mx_5 <= 1000000000)) (PreH15 : (all_4 = mx_5)) (PreH16 : (1 <= q_3)) (PreH17 : (q_3 <= 31623)) (PreH18 : ((q_3 * q_3 ) <= mx_5)) (PreH19 : ((mx_5 % ( q_3 ) ) = 0)) (PreH20 : (0 <= z_2)) (PreH21 : (z_2 < 2)) (PreH22 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH23 : (1 <= d)) (PreH24 : (d <= mx_5)) (PreH25 : (0 <= ans_3)) (PreH26 : (ans_3 <= n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= present)) (PreH30 : (present <= 1)) (PreH31 : (0 <= count)) (PreH32 : (count <= i)) (PreH33 : (1 <= l)) (PreH34 : (l <= (d + 1 ))) (PreH35 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH36 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH37 : (CopyMaxState original copied n_pre mx_5 )) (PreH38 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH39 : (Permutation copied sorted )) (PreH40 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH41 : (DivisorScanState sorted d i present count l )) (PreH42 : (z < 2)) (PreH43 : (a_5 <> 0)) (PreH44 : (n_pre = (Zlength (original)))) (PreH45 : ((Zlength (copied)) = n_pre)) (PreH46 : ((Zlength (sorted)) = n_pre)) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : (1 <= mx_4)) (PreH50 : (mx_4 <= 1000000000)) (PreH51 : (all_3 = mx_4)) (PreH52 : (1 <= q_2)) (PreH53 : (q_2 <= 31623)) (PreH54 : ((q_2 * q_2 ) <= mx_4)) (PreH55 : ((mx_4 % ( q_2 ) ) = 0)) (PreH56 : (0 <= z)) (PreH57 : (z <= 2)) (PreH58 : (0 <= ans_2)) (PreH59 : (ans_2 <= n_pre)) (PreH60 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH61 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH62 : (CopyMaxState original copied n_pre mx_4 )) (PreH63 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH64 : (Permutation copied sorted )) (PreH65 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH66 : ((mx_3 % ( q ) ) = 0)) (PreH67 : ((q * q ) <= mx_3)) (PreH68 : (a_4 <> 0)) (PreH69 : (n_pre = (Zlength (original)))) (PreH70 : ((Zlength (copied)) = n_pre)) (PreH71 : ((Zlength (sorted)) = n_pre)) (PreH72 : (1 <= n_pre)) (PreH73 : (n_pre <= 2000)) (PreH74 : (1 <= mx_3)) (PreH75 : (mx_3 <= 1000000000)) (PreH76 : (all_2 = mx_3)) (PreH77 : (1 <= q)) (PreH78 : (q <= 31624)) (PreH79 : (0 <= ans)) (PreH80 : (ans <= n_pre)) (PreH81 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH82 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH83 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH84 : (CopyMaxState original copied n_pre mx_3 )) (PreH85 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH86 : (Permutation copied sorted )) (PreH87 : (DivisorBestState original mx_3 q 0 ans )) (PreH88 : (a_3 <> 0)) (PreH89 : (n_pre = (Zlength (original)))) (PreH90 : ((Zlength (copied)) = n_pre)) (PreH91 : ((Zlength (sorted)) = n_pre)) (PreH92 : (1 <= n_pre)) (PreH93 : (n_pre <= 2000)) (PreH94 : (1 <= all)) (PreH95 : (all <= 1000000000)) (PreH96 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH97 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH98 : (CopyMaxState original copied n_pre all )) (PreH99 : (LcmPrefixState copied n_pre all all )) (PreH100 : (Permutation copied sorted )) (PreH101 : (Permutation copied sorted )) (PreH102 : ((Zlength (sorted)) = n_pre)) (PreH103 : (all = mx_2)) (PreH104 : (i_2 >= n_pre)) (PreH105 : (a_3 <> 0)) (PreH106 : (n_pre = (Zlength (original)))) (PreH107 : ((Zlength (copied)) = n_pre)) (PreH108 : (1 <= n_pre)) (PreH109 : (n_pre <= 2000)) (PreH110 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH111 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH112 : (1 <= mx_2)) (PreH113 : (mx_2 <= 1000000000)) (PreH114 : (0 <= i_2)) (PreH115 : (i_2 <= n_pre)) (PreH116 : (1 <= all)) (PreH117 : (all <= (mx_2 + 1 ))) (PreH118 : (CopyMaxState original copied n_pre mx_2 )) (PreH119 : (LcmPrefixState copied i_2 mx_2 all )) (PreH120 : (finished_i >= n_pre)) (PreH121 : (a_2 <> 0)) (PreH122 : (n_pre = (Zlength (original)))) (PreH123 : (1 <= n_pre)) (PreH124 : (n_pre <= 2000)) (PreH125 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH126 : (0 <= finished_i)) (PreH127 : (finished_i <= n_pre)) (PreH128 : (0 <= mx)) (PreH129 : (mx <= 1000000000)) (PreH130 : (CopyMaxState original copied finished_i mx )) (PreH131 : (retval <> 0)) (PreH132 : (original = a)) (PreH133 : (n_pre = (Zlength (original)))) (PreH134 : (1 <= n_pre)) (PreH135 : (n_pre <= 2000)) (PreH136 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "present" ) )) # Int  |-> present)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "l" ) )) # Int64  |-> retval_2)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i sorted 0) ) ) <> 0)) (PreH2 : ((Znth i sorted 0) = d)) (PreH3 : (i < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i_2 >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i_2)) (PreH112 : (i_2 <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i_2 mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "present" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i sorted 0) ) ) <> 0)) (PreH2 : ((Znth i sorted 0) <> d)) (PreH3 : (i < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i_2 >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i_2)) (PreH112 : (i_2 <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i_2 mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "present" ) )) # Int  |-> present)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_31 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z_2: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : (count > ans_3)) (PreH2 : (l = d)) (PreH3 : (present = 0)) (PreH4 : (i_2 >= n_pre)) (PreH5 : (a_6 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (1 <= mx_5)) (PreH12 : (mx_5 <= 1000000000)) (PreH13 : (all_4 = mx_5)) (PreH14 : (1 <= q_3)) (PreH15 : (q_3 <= 31623)) (PreH16 : ((q_3 * q_3 ) <= mx_5)) (PreH17 : ((mx_5 % ( q_3 ) ) = 0)) (PreH18 : (0 <= z)) (PreH19 : (z < 2)) (PreH20 : (d = (Znth z (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH21 : (1 <= d)) (PreH22 : (d <= mx_5)) (PreH23 : (0 <= ans_3)) (PreH24 : (ans_3 <= n_pre)) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 <= n_pre)) (PreH27 : (0 <= present)) (PreH28 : (present <= 1)) (PreH29 : (0 <= count)) (PreH30 : (count <= i_2)) (PreH31 : (1 <= l)) (PreH32 : (l <= (d + 1 ))) (PreH33 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH34 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH35 : (CopyMaxState original copied n_pre mx_5 )) (PreH36 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH37 : (Permutation copied sorted )) (PreH38 : (DivisorBestState original mx_5 q_3 z ans_3 )) (PreH39 : (DivisorScanState sorted d i_2 present count l )) (PreH40 : (z_2 < 2)) (PreH41 : (a_5 <> 0)) (PreH42 : (n_pre = (Zlength (original)))) (PreH43 : ((Zlength (copied)) = n_pre)) (PreH44 : ((Zlength (sorted)) = n_pre)) (PreH45 : (1 <= n_pre)) (PreH46 : (n_pre <= 2000)) (PreH47 : (1 <= mx_4)) (PreH48 : (mx_4 <= 1000000000)) (PreH49 : (all_3 = mx_4)) (PreH50 : (1 <= q_2)) (PreH51 : (q_2 <= 31623)) (PreH52 : ((q_2 * q_2 ) <= mx_4)) (PreH53 : ((mx_4 % ( q_2 ) ) = 0)) (PreH54 : (0 <= z_2)) (PreH55 : (z_2 <= 2)) (PreH56 : (0 <= ans_2)) (PreH57 : (ans_2 <= n_pre)) (PreH58 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH59 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH60 : (CopyMaxState original copied n_pre mx_4 )) (PreH61 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH62 : (Permutation copied sorted )) (PreH63 : (DivisorBestState original mx_4 q_2 z_2 ans_2 )) (PreH64 : ((mx_3 % ( q ) ) = 0)) (PreH65 : ((q * q ) <= mx_3)) (PreH66 : (a_4 <> 0)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : ((Zlength (copied)) = n_pre)) (PreH69 : ((Zlength (sorted)) = n_pre)) (PreH70 : (1 <= n_pre)) (PreH71 : (n_pre <= 2000)) (PreH72 : (1 <= mx_3)) (PreH73 : (mx_3 <= 1000000000)) (PreH74 : (all_2 = mx_3)) (PreH75 : (1 <= q)) (PreH76 : (q <= 31624)) (PreH77 : (0 <= ans)) (PreH78 : (ans <= n_pre)) (PreH79 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH80 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH81 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH82 : (CopyMaxState original copied n_pre mx_3 )) (PreH83 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH84 : (Permutation copied sorted )) (PreH85 : (DivisorBestState original mx_3 q 0 ans )) (PreH86 : (a_3 <> 0)) (PreH87 : (n_pre = (Zlength (original)))) (PreH88 : ((Zlength (copied)) = n_pre)) (PreH89 : ((Zlength (sorted)) = n_pre)) (PreH90 : (1 <= n_pre)) (PreH91 : (n_pre <= 2000)) (PreH92 : (1 <= all)) (PreH93 : (all <= 1000000000)) (PreH94 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH95 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH96 : (CopyMaxState original copied n_pre all )) (PreH97 : (LcmPrefixState copied n_pre all all )) (PreH98 : (Permutation copied sorted )) (PreH99 : (Permutation copied sorted )) (PreH100 : ((Zlength (sorted)) = n_pre)) (PreH101 : (all = mx_2)) (PreH102 : (i >= n_pre)) (PreH103 : (a_3 <> 0)) (PreH104 : (n_pre = (Zlength (original)))) (PreH105 : ((Zlength (copied)) = n_pre)) (PreH106 : (1 <= n_pre)) (PreH107 : (n_pre <= 2000)) (PreH108 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH109 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH110 : (1 <= mx_2)) (PreH111 : (mx_2 <= 1000000000)) (PreH112 : (0 <= i)) (PreH113 : (i <= n_pre)) (PreH114 : (1 <= all)) (PreH115 : (all <= (mx_2 + 1 ))) (PreH116 : (CopyMaxState original copied n_pre mx_2 )) (PreH117 : (LcmPrefixState copied i mx_2 all )) (PreH118 : (finished_i >= n_pre)) (PreH119 : (a_2 <> 0)) (PreH120 : (n_pre = (Zlength (original)))) (PreH121 : (1 <= n_pre)) (PreH122 : (n_pre <= 2000)) (PreH123 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH124 : (0 <= finished_i)) (PreH125 : (finished_i <= n_pre)) (PreH126 : (0 <= mx)) (PreH127 : (mx <= 1000000000)) (PreH128 : (CopyMaxState original copied finished_i mx )) (PreH129 : (retval <> 0)) (PreH130 : (original = a)) (PreH131 : (n_pre = (Zlength (original)))) (PreH132 : (1 <= n_pre)) (PreH133 : (n_pre <= 2000)) (PreH134 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ans" ) )) # Int  |-> count)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((z + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (z + 1 )) ”
.

Definition solver_safety_wit_32 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z_2: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : (l <> d)) (PreH2 : (present = 0)) (PreH3 : (i_2 >= n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z)) (PreH18 : (z < 2)) (PreH19 : (d = (Znth z (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z_2 < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z_2)) (PreH54 : (z_2 <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z_2 ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((z + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (z + 1 )) ”
.

Definition solver_safety_wit_33 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z_2: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : (present <> 0)) (PreH2 : (i_2 >= n_pre)) (PreH3 : (a_6 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_5)) (PreH10 : (mx_5 <= 1000000000)) (PreH11 : (all_4 = mx_5)) (PreH12 : (1 <= q_3)) (PreH13 : (q_3 <= 31623)) (PreH14 : ((q_3 * q_3 ) <= mx_5)) (PreH15 : ((mx_5 % ( q_3 ) ) = 0)) (PreH16 : (0 <= z)) (PreH17 : (z < 2)) (PreH18 : (d = (Znth z (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_5)) (PreH21 : (0 <= ans_3)) (PreH22 : (ans_3 <= n_pre)) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i_2)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_5 )) (PreH34 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_5 q_3 z ans_3 )) (PreH37 : (DivisorScanState sorted d i_2 present count l )) (PreH38 : (z_2 < 2)) (PreH39 : (a_5 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_4)) (PreH46 : (mx_4 <= 1000000000)) (PreH47 : (all_3 = mx_4)) (PreH48 : (1 <= q_2)) (PreH49 : (q_2 <= 31623)) (PreH50 : ((q_2 * q_2 ) <= mx_4)) (PreH51 : ((mx_4 % ( q_2 ) ) = 0)) (PreH52 : (0 <= z_2)) (PreH53 : (z_2 <= 2)) (PreH54 : (0 <= ans_2)) (PreH55 : (ans_2 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_4 )) (PreH59 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_4 q_2 z_2 ans_2 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i)) (PreH111 : (i <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((z + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (z + 1 )) ”
.

Definition solver_safety_wit_34 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z_2: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : (count <= ans_3)) (PreH2 : (l = d)) (PreH3 : (present = 0)) (PreH4 : (i_2 >= n_pre)) (PreH5 : (a_6 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (1 <= mx_5)) (PreH12 : (mx_5 <= 1000000000)) (PreH13 : (all_4 = mx_5)) (PreH14 : (1 <= q_3)) (PreH15 : (q_3 <= 31623)) (PreH16 : ((q_3 * q_3 ) <= mx_5)) (PreH17 : ((mx_5 % ( q_3 ) ) = 0)) (PreH18 : (0 <= z)) (PreH19 : (z < 2)) (PreH20 : (d = (Znth z (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH21 : (1 <= d)) (PreH22 : (d <= mx_5)) (PreH23 : (0 <= ans_3)) (PreH24 : (ans_3 <= n_pre)) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 <= n_pre)) (PreH27 : (0 <= present)) (PreH28 : (present <= 1)) (PreH29 : (0 <= count)) (PreH30 : (count <= i_2)) (PreH31 : (1 <= l)) (PreH32 : (l <= (d + 1 ))) (PreH33 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH34 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH35 : (CopyMaxState original copied n_pre mx_5 )) (PreH36 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH37 : (Permutation copied sorted )) (PreH38 : (DivisorBestState original mx_5 q_3 z ans_3 )) (PreH39 : (DivisorScanState sorted d i_2 present count l )) (PreH40 : (z_2 < 2)) (PreH41 : (a_5 <> 0)) (PreH42 : (n_pre = (Zlength (original)))) (PreH43 : ((Zlength (copied)) = n_pre)) (PreH44 : ((Zlength (sorted)) = n_pre)) (PreH45 : (1 <= n_pre)) (PreH46 : (n_pre <= 2000)) (PreH47 : (1 <= mx_4)) (PreH48 : (mx_4 <= 1000000000)) (PreH49 : (all_3 = mx_4)) (PreH50 : (1 <= q_2)) (PreH51 : (q_2 <= 31623)) (PreH52 : ((q_2 * q_2 ) <= mx_4)) (PreH53 : ((mx_4 % ( q_2 ) ) = 0)) (PreH54 : (0 <= z_2)) (PreH55 : (z_2 <= 2)) (PreH56 : (0 <= ans_2)) (PreH57 : (ans_2 <= n_pre)) (PreH58 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH59 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH60 : (CopyMaxState original copied n_pre mx_4 )) (PreH61 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH62 : (Permutation copied sorted )) (PreH63 : (DivisorBestState original mx_4 q_2 z_2 ans_2 )) (PreH64 : ((mx_3 % ( q ) ) = 0)) (PreH65 : ((q * q ) <= mx_3)) (PreH66 : (a_4 <> 0)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : ((Zlength (copied)) = n_pre)) (PreH69 : ((Zlength (sorted)) = n_pre)) (PreH70 : (1 <= n_pre)) (PreH71 : (n_pre <= 2000)) (PreH72 : (1 <= mx_3)) (PreH73 : (mx_3 <= 1000000000)) (PreH74 : (all_2 = mx_3)) (PreH75 : (1 <= q)) (PreH76 : (q <= 31624)) (PreH77 : (0 <= ans)) (PreH78 : (ans <= n_pre)) (PreH79 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH80 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH81 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH82 : (CopyMaxState original copied n_pre mx_3 )) (PreH83 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH84 : (Permutation copied sorted )) (PreH85 : (DivisorBestState original mx_3 q 0 ans )) (PreH86 : (a_3 <> 0)) (PreH87 : (n_pre = (Zlength (original)))) (PreH88 : ((Zlength (copied)) = n_pre)) (PreH89 : ((Zlength (sorted)) = n_pre)) (PreH90 : (1 <= n_pre)) (PreH91 : (n_pre <= 2000)) (PreH92 : (1 <= all)) (PreH93 : (all <= 1000000000)) (PreH94 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH95 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH96 : (CopyMaxState original copied n_pre all )) (PreH97 : (LcmPrefixState copied n_pre all all )) (PreH98 : (Permutation copied sorted )) (PreH99 : (Permutation copied sorted )) (PreH100 : ((Zlength (sorted)) = n_pre)) (PreH101 : (all = mx_2)) (PreH102 : (i >= n_pre)) (PreH103 : (a_3 <> 0)) (PreH104 : (n_pre = (Zlength (original)))) (PreH105 : ((Zlength (copied)) = n_pre)) (PreH106 : (1 <= n_pre)) (PreH107 : (n_pre <= 2000)) (PreH108 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH109 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH110 : (1 <= mx_2)) (PreH111 : (mx_2 <= 1000000000)) (PreH112 : (0 <= i)) (PreH113 : (i <= n_pre)) (PreH114 : (1 <= all)) (PreH115 : (all <= (mx_2 + 1 ))) (PreH116 : (CopyMaxState original copied n_pre mx_2 )) (PreH117 : (LcmPrefixState copied i mx_2 all )) (PreH118 : (finished_i >= n_pre)) (PreH119 : (a_2 <> 0)) (PreH120 : (n_pre = (Zlength (original)))) (PreH121 : (1 <= n_pre)) (PreH122 : (n_pre <= 2000)) (PreH123 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH124 : (0 <= finished_i)) (PreH125 : (finished_i <= n_pre)) (PreH126 : (0 <= mx)) (PreH127 : (mx <= 1000000000)) (PreH128 : (CopyMaxState original copied finished_i mx )) (PreH129 : (retval <> 0)) (PreH130 : (original = a)) (PreH131 : (n_pre = (Zlength (original)))) (PreH132 : (1 <= n_pre)) (PreH133 : (n_pre <= 2000)) (PreH134 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((z + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (z + 1 )) ”
.

Definition solver_safety_wit_35 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q_2: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z >= 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q)) (PreH12 : (q <= 31623)) (PreH13 : ((q * q ) <= mx_4)) (PreH14 : ((mx_4 % ( q ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q z ans_2 )) (PreH25 : ((mx_3 % ( q_2 ) ) = 0)) (PreH26 : ((q_2 * q_2 ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q_2)) (PreH37 : (q_2 <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q_2 - 1 ) * (q_2 - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q_2 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_5)
  **  ((( &( "mx" ) )) # Int  |-> mx_4)
  **  ((( &( "all" ) )) # Int64  |-> all_3)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int  |-> ans_2)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
|--
  “ ((q + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_safety_wit_36 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((mx_3 % ( q ) ) <> 0)) (PreH2 : ((q * q ) <= mx_3)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_3)) (PreH10 : (mx_3 <= 1000000000)) (PreH11 : (all_2 = mx_3)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx_3 )) (PreH20 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx_3 q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_2)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_2)) (PreH48 : (mx_2 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_2 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_2 )) (PreH54 : (LcmPrefixState copied i mx_2 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx)) (PreH64 : (mx <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_4)
  **  ((( &( "mx" ) )) # Int  |-> mx_3)
  **  ((( &( "all" ) )) # Int64  |-> all_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ ((q + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (PreH1 : (1 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 2000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  (IntArray.full input_pre n_pre a )
|--
  EX (original: (@list Z)) ,
  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (PreH1 : (1 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 2000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (PreH1 : (1 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 2000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_2 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (PreH1 : (retval <> 0)) (PreH2 : (original = a)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.undef_full retval n_pre )
  **  (IntArray.full input_pre n_pre original )
|--
  EX (copied: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (CopyMaxState original copied 0 0 ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.seg retval 0 0 copied )
  **  (IntArray.undef_seg retval 0 n_pre )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (PreH1 : (retval <> 0)) (PreH2 : (original = a)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (CopyMaxState a (@nil Z) 0 0 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (PreH1 : (retval <> 0)) (PreH2 : (original = a)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (CopyMaxState a (@nil Z) 0 0 )
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (PreH1 : (retval <> 0)) (PreH2 : (original = a)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))
.

Definition solver_entail_wit_3_1 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied_2: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : ((Znth (i - 0 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) 0) > mx)) (PreH2 : (i < n_pre)) (PreH3 : (a_2 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= mx)) (PreH11 : (mx <= 1000000000)) (PreH12 : (CopyMaxState original copied_2 i mx )) (PreH13 : (retval <> 0)) (PreH14 : (original = a)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.seg a_2 0 (i + 1 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
  **  (IntArray.full input_pre n_pre original )
|--
  EX (copied: (@list Z)) ,
  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (Znth (i - 0 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) 0)) ” 
  &&  “ ((Znth (i - 0 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) 0) <= 1000000000) ” 
  &&  “ (CopyMaxState original copied (i + 1 ) (Znth (i - 0 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) 0) ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.seg a_2 0 (i + 1 ) copied )
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied_2: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : ((Znth (i - 0 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) 0) > mx)) (PreH2 : (i < n_pre)) (PreH3 : (a_2 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= mx)) (PreH11 : (mx <= 1000000000)) (PreH12 : (CopyMaxState original copied_2 i mx )) (PreH13 : (retval <> 0)) (PreH14 : (original = a)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (CopyMaxState a (app (copied_2) ((cons ((Znth i a 0)) ((@nil Z))))) (i + 1 ) (Znth (i - 0 ) (app (copied_2) ((cons ((Znth i a 0)) ((@nil Z))))) 0) ) ” 
  &&  “ ((Znth (i - 0 ) (app (copied_2) ((cons ((Znth i a 0)) ((@nil Z))))) 0) <= 1000000000) ”
  &&  emp
).

Definition solver_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied_2: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : ((Znth (i - 0 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) 0) > mx)) (PreH2 : (i < n_pre)) (PreH3 : (a_2 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= mx)) (PreH11 : (mx <= 1000000000)) (PreH12 : (CopyMaxState original copied_2 i mx )) (PreH13 : (retval <> 0)) (PreH14 : (original = a)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (CopyMaxState a (app (copied_2) ((cons ((Znth i a 0)) ((@nil Z))))) (i + 1 ) (Znth (i - 0 ) (app (copied_2) ((cons ((Znth i a 0)) ((@nil Z))))) 0) )
.

Definition solver_entail_wit_3_1_split_goal_2 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied_2: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : ((Znth (i - 0 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) 0) > mx)) (PreH2 : (i < n_pre)) (PreH3 : (a_2 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= mx)) (PreH11 : (mx <= 1000000000)) (PreH12 : (CopyMaxState original copied_2 i mx )) (PreH13 : (retval <> 0)) (PreH14 : (original = a)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((Znth (i - 0 ) (app (copied_2) ((cons ((Znth i a 0)) ((@nil Z))))) 0) <= 1000000000)
.

Definition solver_entail_wit_3_2 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied_2: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : ((Znth (i - 0 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) 0) <= mx)) (PreH2 : (i < n_pre)) (PreH3 : (a_2 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= mx)) (PreH11 : (mx <= 1000000000)) (PreH12 : (CopyMaxState original copied_2 i mx )) (PreH13 : (retval <> 0)) (PreH14 : (original = a)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.seg a_2 0 (i + 1 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
  **  (IntArray.full input_pre n_pre original )
|--
  EX (copied: (@list Z)) ,
  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied (i + 1 ) mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.seg a_2 0 (i + 1 ) copied )
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied_2: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : ((Znth (i - 0 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) 0) <= mx)) (PreH2 : (i < n_pre)) (PreH3 : (a_2 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= mx)) (PreH11 : (mx <= 1000000000)) (PreH12 : (CopyMaxState original copied_2 i mx )) (PreH13 : (retval <> 0)) (PreH14 : (original = a)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (CopyMaxState a (app (copied_2) ((cons ((Znth i a 0)) ((@nil Z))))) (i + 1 ) mx ) ”
  &&  emp
).

Definition solver_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied_2: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : ((Znth (i - 0 ) (app (copied_2) ((cons ((Znth i original 0)) ((@nil Z))))) 0) <= mx)) (PreH2 : (i < n_pre)) (PreH3 : (a_2 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= mx)) (PreH11 : (mx <= 1000000000)) (PreH12 : (CopyMaxState original copied_2 i mx )) (PreH13 : (retval <> 0)) (PreH14 : (original = a)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (CopyMaxState a (app (copied_2) ((cons ((Znth i a 0)) ((@nil Z))))) (i + 1 ) mx )
.

Definition solver_entail_wit_4 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_2 n_pre copied )
  **  (IntArray.full input_pre n_pre original )
|--
  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (mx + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx ) ” 
  &&  “ (LcmPrefixState copied 0 mx 1 ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_2 n_pre copied )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (LcmPrefixState copied 0 mx 1 ) ” 
  &&  “ (CopyMaxState a copied n_pre mx ) ” 
  &&  “ (1 <= mx) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (LcmPrefixState copied 0 mx 1 )
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (CopyMaxState a copied n_pre mx )
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (1 <= mx)
.

Definition solver_entail_wit_4_split_goal_4 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))
.

Definition solver_entail_wit_4_split_goal_5 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))
.

Definition solver_entail_wit_4_split_goal_6 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((Zlength (copied)) = n_pre)
.

Definition solver_entail_wit_5 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (mx_2 + 1 ))) (PreH3 : (LcmCapValue all (Znth i copied 0) mx_2 retval_2 )) (PreH4 : (i < n_pre)) (PreH5 : (a_3 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH12 : (1 <= mx_2)) (PreH13 : (mx_2 <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (1 <= all)) (PreH17 : (all <= (mx_2 + 1 ))) (PreH18 : (CopyMaxState original copied n_pre mx_2 )) (PreH19 : (LcmPrefixState copied i mx_2 all )) (PreH20 : (finished_i >= n_pre)) (PreH21 : (a_2 <> 0)) (PreH22 : (n_pre = (Zlength (original)))) (PreH23 : (1 <= n_pre)) (PreH24 : (n_pre <= 2000)) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH26 : (0 <= finished_i)) (PreH27 : (finished_i <= n_pre)) (PreH28 : (0 <= mx)) (PreH29 : (mx <= 1000000000)) (PreH30 : (CopyMaxState original copied finished_i mx )) (PreH31 : (retval <> 0)) (PreH32 : (original = a)) (PreH33 : (n_pre = (Zlength (original)))) (PreH34 : (1 <= n_pre)) (PreH35 : (n_pre <= 2000)) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_3 n_pre copied )
  **  (IntArray.full input_pre n_pre original )
|--
  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (1 <= retval_2) ” 
  &&  “ (retval_2 <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied (i + 1 ) mx_2 retval_2 ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre copied )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (mx_2 + 1 ))) (PreH3 : (LcmCapValue all (Znth i copied 0) mx_2 retval_2 )) (PreH4 : (i < n_pre)) (PreH5 : (a_3 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH12 : (1 <= mx_2)) (PreH13 : (mx_2 <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (1 <= all)) (PreH17 : (all <= (mx_2 + 1 ))) (PreH18 : (CopyMaxState original copied n_pre mx_2 )) (PreH19 : (LcmPrefixState copied i mx_2 all )) (PreH20 : (finished_i >= n_pre)) (PreH21 : (a_2 <> 0)) (PreH22 : (n_pre = (Zlength (original)))) (PreH23 : (1 <= n_pre)) (PreH24 : (n_pre <= 2000)) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH26 : (0 <= finished_i)) (PreH27 : (finished_i <= n_pre)) (PreH28 : (0 <= mx)) (PreH29 : (mx <= 1000000000)) (PreH30 : (CopyMaxState original copied finished_i mx )) (PreH31 : (retval <> 0)) (PreH32 : (original = a)) (PreH33 : (n_pre = (Zlength (original)))) (PreH34 : (1 <= n_pre)) (PreH35 : (n_pre <= 2000)) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (LcmPrefixState copied (i + 1 ) mx_2 retval_2 ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (mx_2 + 1 ))) (PreH3 : (LcmCapValue all (Znth i copied 0) mx_2 retval_2 )) (PreH4 : (i < n_pre)) (PreH5 : (a_3 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH12 : (1 <= mx_2)) (PreH13 : (mx_2 <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (1 <= all)) (PreH17 : (all <= (mx_2 + 1 ))) (PreH18 : (CopyMaxState original copied n_pre mx_2 )) (PreH19 : (LcmPrefixState copied i mx_2 all )) (PreH20 : (finished_i >= n_pre)) (PreH21 : (a_2 <> 0)) (PreH22 : (n_pre = (Zlength (original)))) (PreH23 : (1 <= n_pre)) (PreH24 : (n_pre <= 2000)) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH26 : (0 <= finished_i)) (PreH27 : (finished_i <= n_pre)) (PreH28 : (0 <= mx)) (PreH29 : (mx <= 1000000000)) (PreH30 : (CopyMaxState original copied finished_i mx )) (PreH31 : (retval <> 0)) (PreH32 : (original = a)) (PreH33 : (n_pre = (Zlength (original)))) (PreH34 : (1 <= n_pre)) (PreH35 : (n_pre <= 2000)) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (LcmPrefixState copied (i + 1 ) mx_2 retval_2 )
.

Definition solver_entail_wit_6 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (PreH1 : (all <> mx_2)) (PreH2 : (i >= n_pre)) (PreH3 : (a_3 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH10 : (1 <= mx_2)) (PreH11 : (mx_2 <= 1000000000)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= all)) (PreH15 : (all <= (mx_2 + 1 ))) (PreH16 : (CopyMaxState original copied n_pre mx_2 )) (PreH17 : (LcmPrefixState copied i mx_2 all )) (PreH18 : (finished_i >= n_pre)) (PreH19 : (a_2 <> 0)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH24 : (0 <= finished_i)) (PreH25 : (finished_i <= n_pre)) (PreH26 : (0 <= mx)) (PreH27 : (mx <= 1000000000)) (PreH28 : (CopyMaxState original copied finished_i mx )) (PreH29 : (retval <> 0)) (PreH30 : (original = a)) (PreH31 : (n_pre = (Zlength (original)))) (PreH32 : (1 <= n_pre)) (PreH33 : (n_pre <= 2000)) (PreH34 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre copied )
|--
  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (all <> mx_2) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_2 all ) ” 
  &&  “ (Spec original n_pre ) ” 
  &&  “ (all <> mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre copied )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (PreH1 : (all <> mx_2)) (PreH2 : (i >= n_pre)) (PreH3 : (a_3 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH10 : (1 <= mx_2)) (PreH11 : (mx_2 <= 1000000000)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= all)) (PreH15 : (all <= (mx_2 + 1 ))) (PreH16 : (CopyMaxState original copied n_pre mx_2 )) (PreH17 : (LcmPrefixState copied i mx_2 all )) (PreH18 : (finished_i >= n_pre)) (PreH19 : (a_2 <> 0)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH24 : (0 <= finished_i)) (PreH25 : (finished_i <= n_pre)) (PreH26 : (0 <= mx)) (PreH27 : (mx <= 1000000000)) (PreH28 : (CopyMaxState original copied finished_i mx )) (PreH29 : (retval <> 0)) (PreH30 : (original = a)) (PreH31 : (n_pre = (Zlength (original)))) (PreH32 : (1 <= n_pre)) (PreH33 : (n_pre <= 2000)) (PreH34 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (Spec a n_pre ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_2 all ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (PreH1 : (all <> mx_2)) (PreH2 : (i >= n_pre)) (PreH3 : (a_3 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH10 : (1 <= mx_2)) (PreH11 : (mx_2 <= 1000000000)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= all)) (PreH15 : (all <= (mx_2 + 1 ))) (PreH16 : (CopyMaxState original copied n_pre mx_2 )) (PreH17 : (LcmPrefixState copied i mx_2 all )) (PreH18 : (finished_i >= n_pre)) (PreH19 : (a_2 <> 0)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH24 : (0 <= finished_i)) (PreH25 : (finished_i <= n_pre)) (PreH26 : (0 <= mx)) (PreH27 : (mx <= 1000000000)) (PreH28 : (CopyMaxState original copied finished_i mx )) (PreH29 : (retval <> 0)) (PreH30 : (original = a)) (PreH31 : (n_pre = (Zlength (original)))) (PreH32 : (1 <= n_pre)) (PreH33 : (n_pre <= 2000)) (PreH34 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (Spec a n_pre )
.

Definition solver_entail_wit_6_split_goal_2 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (PreH1 : (all <> mx_2)) (PreH2 : (i >= n_pre)) (PreH3 : (a_3 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH10 : (1 <= mx_2)) (PreH11 : (mx_2 <= 1000000000)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= all)) (PreH15 : (all <= (mx_2 + 1 ))) (PreH16 : (CopyMaxState original copied n_pre mx_2 )) (PreH17 : (LcmPrefixState copied i mx_2 all )) (PreH18 : (finished_i >= n_pre)) (PreH19 : (a_2 <> 0)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH24 : (0 <= finished_i)) (PreH25 : (finished_i <= n_pre)) (PreH26 : (0 <= mx)) (PreH27 : (mx <= 1000000000)) (PreH28 : (CopyMaxState original copied finished_i mx )) (PreH29 : (retval <> 0)) (PreH30 : (original = a)) (PreH31 : (n_pre = (Zlength (original)))) (PreH32 : (1 <= n_pre)) (PreH33 : (n_pre <= 2000)) (PreH34 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (LcmPrefixState copied n_pre mx_2 all )
.

Definition solver_entail_wit_7 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (Permutation copied sorted )) (PreH2 : ((Zlength (sorted)) = n_pre)) (PreH3 : (all = mx_2)) (PreH4 : (i >= n_pre)) (PreH5 : (a_3 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH12 : (1 <= mx_2)) (PreH13 : (mx_2 <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (1 <= all)) (PreH17 : (all <= (mx_2 + 1 ))) (PreH18 : (CopyMaxState original copied n_pre mx_2 )) (PreH19 : (LcmPrefixState copied i mx_2 all )) (PreH20 : (finished_i >= n_pre)) (PreH21 : (a_2 <> 0)) (PreH22 : (n_pre = (Zlength (original)))) (PreH23 : (1 <= n_pre)) (PreH24 : (n_pre <= 2000)) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH26 : (0 <= finished_i)) (PreH27 : (finished_i <= n_pre)) (PreH28 : (0 <= mx)) (PreH29 : (mx <= 1000000000)) (PreH30 : (CopyMaxState original copied finished_i mx )) (PreH31 : (retval <> 0)) (PreH32 : (original = a)) (PreH33 : (n_pre = (Zlength (original)))) (PreH34 : (1 <= n_pre)) (PreH35 : (n_pre <= 2000)) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_3 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
|--
  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ (all = all) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = all) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (all + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied i all all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre sorted )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (Permutation copied sorted )) (PreH2 : ((Zlength (sorted)) = n_pre)) (PreH3 : (all = mx_2)) (PreH4 : (i >= n_pre)) (PreH5 : (a_3 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH12 : (1 <= mx_2)) (PreH13 : (mx_2 <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (1 <= all)) (PreH17 : (all <= (mx_2 + 1 ))) (PreH18 : (CopyMaxState original copied n_pre mx_2 )) (PreH19 : (LcmPrefixState copied i mx_2 all )) (PreH20 : (finished_i >= n_pre)) (PreH21 : (a_2 <> 0)) (PreH22 : (n_pre = (Zlength (original)))) (PreH23 : (1 <= n_pre)) (PreH24 : (n_pre <= 2000)) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH26 : (0 <= finished_i)) (PreH27 : (finished_i <= n_pre)) (PreH28 : (0 <= mx)) (PreH29 : (mx <= 1000000000)) (PreH30 : (CopyMaxState original copied finished_i mx )) (PreH31 : (retval <> 0)) (PreH32 : (original = a)) (PreH33 : (n_pre = (Zlength (original)))) (PreH34 : (1 <= n_pre)) (PreH35 : (n_pre <= 2000)) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (Permutation copied sorted )) (PreH2 : ((Zlength (sorted)) = n_pre)) (PreH3 : (all = mx_2)) (PreH4 : (i >= n_pre)) (PreH5 : (a_3 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH12 : (1 <= mx_2)) (PreH13 : (mx_2 <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (1 <= all)) (PreH17 : (all <= (mx_2 + 1 ))) (PreH18 : (CopyMaxState original copied n_pre mx_2 )) (PreH19 : (LcmPrefixState copied i mx_2 all )) (PreH20 : (finished_i >= n_pre)) (PreH21 : (a_2 <> 0)) (PreH22 : (n_pre = (Zlength (original)))) (PreH23 : (1 <= n_pre)) (PreH24 : (n_pre <= 2000)) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH26 : (0 <= finished_i)) (PreH27 : (finished_i <= n_pre)) (PreH28 : (0 <= mx)) (PreH29 : (mx <= 1000000000)) (PreH30 : (CopyMaxState original copied finished_i mx )) (PreH31 : (retval <> 0)) (PreH32 : (original = a)) (PreH33 : (n_pre = (Zlength (original)))) (PreH34 : (1 <= n_pre)) (PreH35 : (n_pre <= 2000)) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (LcmPrefixState copied n_pre all all )
.

Definition solver_entail_wit_7_split_goal_2 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (Permutation copied sorted )) (PreH2 : ((Zlength (sorted)) = n_pre)) (PreH3 : (all = mx_2)) (PreH4 : (i >= n_pre)) (PreH5 : (a_3 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH12 : (1 <= mx_2)) (PreH13 : (mx_2 <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (1 <= all)) (PreH17 : (all <= (mx_2 + 1 ))) (PreH18 : (CopyMaxState original copied n_pre mx_2 )) (PreH19 : (LcmPrefixState copied i mx_2 all )) (PreH20 : (finished_i >= n_pre)) (PreH21 : (a_2 <> 0)) (PreH22 : (n_pre = (Zlength (original)))) (PreH23 : (1 <= n_pre)) (PreH24 : (n_pre <= 2000)) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH26 : (0 <= finished_i)) (PreH27 : (finished_i <= n_pre)) (PreH28 : (0 <= mx)) (PreH29 : (mx <= 1000000000)) (PreH30 : (CopyMaxState original copied finished_i mx )) (PreH31 : (retval <> 0)) (PreH32 : (original = a)) (PreH33 : (n_pre = (Zlength (original)))) (PreH34 : (1 <= n_pre)) (PreH35 : (n_pre <= 2000)) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))
.

Definition solver_entail_wit_7_split_goal_3 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (Permutation copied sorted )) (PreH2 : ((Zlength (sorted)) = n_pre)) (PreH3 : (all = mx_2)) (PreH4 : (i >= n_pre)) (PreH5 : (a_3 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH12 : (1 <= mx_2)) (PreH13 : (mx_2 <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (1 <= all)) (PreH17 : (all <= (mx_2 + 1 ))) (PreH18 : (CopyMaxState original copied n_pre mx_2 )) (PreH19 : (LcmPrefixState copied i mx_2 all )) (PreH20 : (finished_i >= n_pre)) (PreH21 : (a_2 <> 0)) (PreH22 : (n_pre = (Zlength (original)))) (PreH23 : (1 <= n_pre)) (PreH24 : (n_pre <= 2000)) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH26 : (0 <= finished_i)) (PreH27 : (finished_i <= n_pre)) (PreH28 : (0 <= mx)) (PreH29 : (mx <= 1000000000)) (PreH30 : (CopyMaxState original copied finished_i mx )) (PreH31 : (retval <> 0)) (PreH32 : (original = a)) (PreH33 : (n_pre = (Zlength (original)))) (PreH34 : (1 <= n_pre)) (PreH35 : (n_pre <= 2000)) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))
.

Definition solver_entail_wit_8 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (a_3 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : (1 <= all)) (PreH8 : (all <= 1000000000)) (PreH9 : (all = all)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH12 : (CopyMaxState original copied n_pre all )) (PreH13 : (LcmPrefixState copied n_pre all all )) (PreH14 : (Permutation copied sorted )) (PreH15 : (Permutation copied sorted )) (PreH16 : ((Zlength (sorted)) = n_pre)) (PreH17 : (all = mx_2)) (PreH18 : (i >= n_pre)) (PreH19 : (a_3 <> 0)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : ((Zlength (copied)) = n_pre)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 2000)) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH26 : (1 <= mx_2)) (PreH27 : (mx_2 <= 1000000000)) (PreH28 : (0 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= all)) (PreH31 : (all <= (mx_2 + 1 ))) (PreH32 : (CopyMaxState original copied n_pre mx_2 )) (PreH33 : (LcmPrefixState copied i mx_2 all )) (PreH34 : (finished_i >= n_pre)) (PreH35 : (a_2 <> 0)) (PreH36 : (n_pre = (Zlength (original)))) (PreH37 : (1 <= n_pre)) (PreH38 : (n_pre <= 2000)) (PreH39 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH40 : (0 <= finished_i)) (PreH41 : (finished_i <= n_pre)) (PreH42 : (0 <= mx)) (PreH43 : (mx <= 1000000000)) (PreH44 : (CopyMaxState original copied finished_i mx )) (PreH45 : (retval <> 0)) (PreH46 : (original = a)) (PreH47 : (n_pre = (Zlength (original)))) (PreH48 : (1 <= n_pre)) (PreH49 : (n_pre <= 2000)) (PreH50 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre sorted )
|--
  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ (all = all) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 31624) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((1 - 1 ) * (1 - 1 ) ) <= all) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original all 1 0 0 ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre sorted )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (a_3 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : (1 <= all)) (PreH8 : (all <= 1000000000)) (PreH9 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH10 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH11 : (CopyMaxState original copied n_pre all )) (PreH12 : (LcmPrefixState copied n_pre all all )) (PreH13 : (Permutation copied sorted )) (PreH14 : (Permutation copied sorted )) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : (all = mx_2)) (PreH17 : (i >= n_pre)) (PreH18 : (a_3 <> 0)) (PreH19 : (n_pre = (Zlength (original)))) (PreH20 : ((Zlength (copied)) = n_pre)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH24 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH25 : (1 <= mx_2)) (PreH26 : (mx_2 <= 1000000000)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (1 <= all)) (PreH30 : (all <= (mx_2 + 1 ))) (PreH31 : (CopyMaxState original copied n_pre mx_2 )) (PreH32 : (LcmPrefixState copied i mx_2 all )) (PreH33 : (finished_i >= n_pre)) (PreH34 : (a_2 <> 0)) (PreH35 : (n_pre = (Zlength (original)))) (PreH36 : (1 <= n_pre)) (PreH37 : (n_pre <= 2000)) (PreH38 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH39 : (0 <= finished_i)) (PreH40 : (finished_i <= n_pre)) (PreH41 : (0 <= mx)) (PreH42 : (mx <= 1000000000)) (PreH43 : (CopyMaxState original copied finished_i mx )) (PreH44 : (retval <> 0)) (PreH45 : (original = a)) (PreH46 : (n_pre = (Zlength (original)))) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorBestState a all 1 0 0 ) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (a_3 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : (1 <= all)) (PreH8 : (all <= 1000000000)) (PreH9 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH10 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH11 : (CopyMaxState original copied n_pre all )) (PreH12 : (LcmPrefixState copied n_pre all all )) (PreH13 : (Permutation copied sorted )) (PreH14 : (Permutation copied sorted )) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : (all = mx_2)) (PreH17 : (i >= n_pre)) (PreH18 : (a_3 <> 0)) (PreH19 : (n_pre = (Zlength (original)))) (PreH20 : ((Zlength (copied)) = n_pre)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH24 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH25 : (1 <= mx_2)) (PreH26 : (mx_2 <= 1000000000)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (1 <= all)) (PreH30 : (all <= (mx_2 + 1 ))) (PreH31 : (CopyMaxState original copied n_pre mx_2 )) (PreH32 : (LcmPrefixState copied i mx_2 all )) (PreH33 : (finished_i >= n_pre)) (PreH34 : (a_2 <> 0)) (PreH35 : (n_pre = (Zlength (original)))) (PreH36 : (1 <= n_pre)) (PreH37 : (n_pre <= 2000)) (PreH38 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH39 : (0 <= finished_i)) (PreH40 : (finished_i <= n_pre)) (PreH41 : (0 <= mx)) (PreH42 : (mx <= 1000000000)) (PreH43 : (CopyMaxState original copied finished_i mx )) (PreH44 : (retval <> 0)) (PreH45 : (original = a)) (PreH46 : (n_pre = (Zlength (original)))) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorBestState a all 1 0 0 )
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (a_3 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : (1 <= all)) (PreH8 : (all <= 1000000000)) (PreH9 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH10 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH11 : (CopyMaxState original copied n_pre all )) (PreH12 : (LcmPrefixState copied n_pre all all )) (PreH13 : (Permutation copied sorted )) (PreH14 : (Permutation copied sorted )) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : (all = mx_2)) (PreH17 : (i >= n_pre)) (PreH18 : (a_3 <> 0)) (PreH19 : (n_pre = (Zlength (original)))) (PreH20 : ((Zlength (copied)) = n_pre)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH24 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH25 : (1 <= mx_2)) (PreH26 : (mx_2 <= 1000000000)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (1 <= all)) (PreH30 : (all <= (mx_2 + 1 ))) (PreH31 : (CopyMaxState original copied n_pre mx_2 )) (PreH32 : (LcmPrefixState copied i mx_2 all )) (PreH33 : (finished_i >= n_pre)) (PreH34 : (a_2 <> 0)) (PreH35 : (n_pre = (Zlength (original)))) (PreH36 : (1 <= n_pre)) (PreH37 : (n_pre <= 2000)) (PreH38 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH39 : (0 <= finished_i)) (PreH40 : (finished_i <= n_pre)) (PreH41 : (0 <= mx)) (PreH42 : (mx <= 1000000000)) (PreH43 : (CopyMaxState original copied finished_i mx )) (PreH44 : (retval <> 0)) (PreH45 : (original = a)) (PreH46 : (n_pre = (Zlength (original)))) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))
.

Definition solver_entail_wit_8_split_goal_3 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (PreH1 : (a_3 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : (1 <= all)) (PreH8 : (all <= 1000000000)) (PreH9 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH10 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH11 : (CopyMaxState original copied n_pre all )) (PreH12 : (LcmPrefixState copied n_pre all all )) (PreH13 : (Permutation copied sorted )) (PreH14 : (Permutation copied sorted )) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : (all = mx_2)) (PreH17 : (i >= n_pre)) (PreH18 : (a_3 <> 0)) (PreH19 : (n_pre = (Zlength (original)))) (PreH20 : ((Zlength (copied)) = n_pre)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH24 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH25 : (1 <= mx_2)) (PreH26 : (mx_2 <= 1000000000)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (1 <= all)) (PreH30 : (all <= (mx_2 + 1 ))) (PreH31 : (CopyMaxState original copied n_pre mx_2 )) (PreH32 : (LcmPrefixState copied i mx_2 all )) (PreH33 : (finished_i >= n_pre)) (PreH34 : (a_2 <> 0)) (PreH35 : (n_pre = (Zlength (original)))) (PreH36 : (1 <= n_pre)) (PreH37 : (n_pre <= 2000)) (PreH38 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH39 : (0 <= finished_i)) (PreH40 : (finished_i <= n_pre)) (PreH41 : (0 <= mx)) (PreH42 : (mx <= 1000000000)) (PreH43 : (CopyMaxState original copied finished_i mx )) (PreH44 : (retval <> 0)) (PreH45 : (original = a)) (PreH46 : (n_pre = (Zlength (original)))) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))
.

Definition solver_entail_wit_9 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((mx_3 % ( q ) ) = 0)) (PreH2 : ((q * q ) <= mx_3)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_3)) (PreH10 : (mx_3 <= 1000000000)) (PreH11 : (all_2 = mx_3)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx_3 )) (PreH20 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx_3 q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_2)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_2)) (PreH48 : (mx_2 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_2 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_2 )) (PreH54 : (LcmPrefixState copied i mx_2 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx)) (PreH64 : (mx <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full ( &( "ds" ) ) 2 (cons (q) ((cons ((mx_3 ÷ q )) ((@nil Z))))) )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31623) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q) ((cons ((mx_3 ÷ q )) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((mx_3 % ( q ) ) = 0)) (PreH2 : ((q * q ) <= mx_3)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_3)) (PreH10 : (mx_3 <= 1000000000)) (PreH11 : (all_2 = mx_3)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx_3 )) (PreH20 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx_3 q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_2)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_2)) (PreH48 : (mx_2 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_2 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_2 )) (PreH54 : (LcmPrefixState copied i mx_2 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx)) (PreH64 : (mx <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((mx_3 % ( q ) ) = 0)) (PreH2 : ((q * q ) <= mx_3)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_3)) (PreH10 : (mx_3 <= 1000000000)) (PreH11 : (all_2 = mx_3)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx_3 )) (PreH20 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx_3 q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_2)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_2)) (PreH48 : (mx_2 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_2 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_2 )) (PreH54 : (LcmPrefixState copied i mx_2 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx)) (PreH64 : (mx <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))
.

Definition solver_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((mx_3 % ( q ) ) = 0)) (PreH2 : ((q * q ) <= mx_3)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_3)) (PreH10 : (mx_3 <= 1000000000)) (PreH11 : (all_2 = mx_3)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx_3 )) (PreH20 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx_3 q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_2)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_2)) (PreH48 : (mx_2 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_2 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_2 )) (PreH54 : (LcmPrefixState copied i mx_2 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx)) (PreH64 : (mx <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))
.

Definition solver_entail_wit_10 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
|--
  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 2) ” 
  &&  “ ((Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0) = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0)) ” 
  &&  “ ((Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0) <= mx_4) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= ((Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0) + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ (DivisorScanState sorted (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0) 0 0 0 1 ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorScanState sorted (Znth z (cons (q_2) ((cons ((all_3 ÷ q_2 )) ((@nil Z))))) 0) 0 0 0 1 ) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ (1 <= ((Znth z (cons (q_2) ((cons ((all_3 ÷ q_2 )) ((@nil Z))))) 0) + 1 )) ” 
  &&  “ ((Znth z (cons (q_2) ((cons ((all_3 ÷ q_2 )) ((@nil Z))))) 0) <= all_3) ” 
  &&  “ (1 <= (Znth z (cons (q_2) ((cons ((all_3 ÷ q_2 )) ((@nil Z))))) 0)) ”
  &&  emp
).

Definition solver_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorScanState sorted (Znth z (cons (q_2) ((cons ((all_3 ÷ q_2 )) ((@nil Z))))) 0) 0 0 0 1 )
.

Definition solver_entail_wit_10_split_goal_2 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))
.

Definition solver_entail_wit_10_split_goal_3 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))
.

Definition solver_entail_wit_10_split_goal_4 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (1 <= ((Znth z (cons (q_2) ((cons ((all_3 ÷ q_2 )) ((@nil Z))))) 0) + 1 ))
.

Definition solver_entail_wit_10_split_goal_5 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((Znth z (cons (q_2) ((cons ((all_3 ÷ q_2 )) ((@nil Z))))) 0) <= all_3)
.

Definition solver_entail_wit_10_split_goal_6 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (1 <= (Znth z (cons (q_2) ((cons ((all_3 ÷ q_2 )) ((@nil Z))))) 0))
.

Definition solver_entail_wit_11_1 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (d + 1 ))) (PreH3 : (LcmCapValue l (Znth i_2 sorted 0) d retval_2 )) (PreH4 : ((d % ( (Znth i_2 sorted 0) ) ) = 0)) (PreH5 : ((Znth i_2 sorted 0) = d)) (PreH6 : (i_2 < n_pre)) (PreH7 : (a_6 <> 0)) (PreH8 : (n_pre = (Zlength (original)))) (PreH9 : ((Zlength (copied)) = n_pre)) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2000)) (PreH13 : (1 <= mx_5)) (PreH14 : (mx_5 <= 1000000000)) (PreH15 : (all_4 = mx_5)) (PreH16 : (1 <= q_3)) (PreH17 : (q_3 <= 31623)) (PreH18 : ((q_3 * q_3 ) <= mx_5)) (PreH19 : ((mx_5 % ( q_3 ) ) = 0)) (PreH20 : (0 <= z_2)) (PreH21 : (z_2 < 2)) (PreH22 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH23 : (1 <= d)) (PreH24 : (d <= mx_5)) (PreH25 : (0 <= ans_3)) (PreH26 : (ans_3 <= n_pre)) (PreH27 : (0 <= i_2)) (PreH28 : (i_2 <= n_pre)) (PreH29 : (0 <= present)) (PreH30 : (present <= 1)) (PreH31 : (0 <= count)) (PreH32 : (count <= i_2)) (PreH33 : (1 <= l)) (PreH34 : (l <= (d + 1 ))) (PreH35 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH36 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH37 : (CopyMaxState original copied n_pre mx_5 )) (PreH38 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH39 : (Permutation copied sorted )) (PreH40 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH41 : (DivisorScanState sorted d i_2 present count l )) (PreH42 : (z < 2)) (PreH43 : (a_5 <> 0)) (PreH44 : (n_pre = (Zlength (original)))) (PreH45 : ((Zlength (copied)) = n_pre)) (PreH46 : ((Zlength (sorted)) = n_pre)) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : (1 <= mx_4)) (PreH50 : (mx_4 <= 1000000000)) (PreH51 : (all_3 = mx_4)) (PreH52 : (1 <= q_2)) (PreH53 : (q_2 <= 31623)) (PreH54 : ((q_2 * q_2 ) <= mx_4)) (PreH55 : ((mx_4 % ( q_2 ) ) = 0)) (PreH56 : (0 <= z)) (PreH57 : (z <= 2)) (PreH58 : (0 <= ans_2)) (PreH59 : (ans_2 <= n_pre)) (PreH60 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH61 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH62 : (CopyMaxState original copied n_pre mx_4 )) (PreH63 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH64 : (Permutation copied sorted )) (PreH65 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH66 : ((mx_3 % ( q ) ) = 0)) (PreH67 : ((q * q ) <= mx_3)) (PreH68 : (a_4 <> 0)) (PreH69 : (n_pre = (Zlength (original)))) (PreH70 : ((Zlength (copied)) = n_pre)) (PreH71 : ((Zlength (sorted)) = n_pre)) (PreH72 : (1 <= n_pre)) (PreH73 : (n_pre <= 2000)) (PreH74 : (1 <= mx_3)) (PreH75 : (mx_3 <= 1000000000)) (PreH76 : (all_2 = mx_3)) (PreH77 : (1 <= q)) (PreH78 : (q <= 31624)) (PreH79 : (0 <= ans)) (PreH80 : (ans <= n_pre)) (PreH81 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH82 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH83 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH84 : (CopyMaxState original copied n_pre mx_3 )) (PreH85 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH86 : (Permutation copied sorted )) (PreH87 : (DivisorBestState original mx_3 q 0 ans )) (PreH88 : (a_3 <> 0)) (PreH89 : (n_pre = (Zlength (original)))) (PreH90 : ((Zlength (copied)) = n_pre)) (PreH91 : ((Zlength (sorted)) = n_pre)) (PreH92 : (1 <= n_pre)) (PreH93 : (n_pre <= 2000)) (PreH94 : (1 <= all)) (PreH95 : (all <= 1000000000)) (PreH96 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH97 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH98 : (CopyMaxState original copied n_pre all )) (PreH99 : (LcmPrefixState copied n_pre all all )) (PreH100 : (Permutation copied sorted )) (PreH101 : (Permutation copied sorted )) (PreH102 : ((Zlength (sorted)) = n_pre)) (PreH103 : (all = mx_2)) (PreH104 : (i >= n_pre)) (PreH105 : (a_3 <> 0)) (PreH106 : (n_pre = (Zlength (original)))) (PreH107 : ((Zlength (copied)) = n_pre)) (PreH108 : (1 <= n_pre)) (PreH109 : (n_pre <= 2000)) (PreH110 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH111 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH112 : (1 <= mx_2)) (PreH113 : (mx_2 <= 1000000000)) (PreH114 : (0 <= i)) (PreH115 : (i <= n_pre)) (PreH116 : (1 <= all)) (PreH117 : (all <= (mx_2 + 1 ))) (PreH118 : (CopyMaxState original copied n_pre mx_2 )) (PreH119 : (LcmPrefixState copied i mx_2 all )) (PreH120 : (finished_i >= n_pre)) (PreH121 : (a_2 <> 0)) (PreH122 : (n_pre = (Zlength (original)))) (PreH123 : (1 <= n_pre)) (PreH124 : (n_pre <= 2000)) (PreH125 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH126 : (0 <= finished_i)) (PreH127 : (finished_i <= n_pre)) (PreH128 : (0 <= mx)) (PreH129 : (mx <= 1000000000)) (PreH130 : (CopyMaxState original copied finished_i mx )) (PreH131 : (retval <> 0)) (PreH132 : (original = a)) (PreH133 : (n_pre = (Zlength (original)))) (PreH134 : (1 <= n_pre)) (PreH135 : (n_pre <= 2000)) (PreH136 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i_2 + 1 )) ” 
  &&  “ (1 <= retval_2) ” 
  &&  “ (retval_2 <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d (i_2 + 1 ) 1 (count + 1 ) retval_2 ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (d + 1 ))) (PreH3 : (LcmCapValue l (Znth i_2 sorted 0) d retval_2 )) (PreH4 : ((d % ( (Znth i_2 sorted 0) ) ) = 0)) (PreH5 : ((Znth i_2 sorted 0) = d)) (PreH6 : (i_2 < n_pre)) (PreH7 : (a_6 <> 0)) (PreH8 : (n_pre = (Zlength (original)))) (PreH9 : ((Zlength (copied)) = n_pre)) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2000)) (PreH13 : (1 <= mx_5)) (PreH14 : (mx_5 <= 1000000000)) (PreH15 : (all_4 = mx_5)) (PreH16 : (1 <= q_3)) (PreH17 : (q_3 <= 31623)) (PreH18 : ((q_3 * q_3 ) <= mx_5)) (PreH19 : ((mx_5 % ( q_3 ) ) = 0)) (PreH20 : (0 <= z_2)) (PreH21 : (z_2 < 2)) (PreH22 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH23 : (1 <= d)) (PreH24 : (d <= mx_5)) (PreH25 : (0 <= ans_3)) (PreH26 : (ans_3 <= n_pre)) (PreH27 : (0 <= i_2)) (PreH28 : (i_2 <= n_pre)) (PreH29 : (0 <= present)) (PreH30 : (present <= 1)) (PreH31 : (0 <= count)) (PreH32 : (count <= i_2)) (PreH33 : (1 <= l)) (PreH34 : (l <= (d + 1 ))) (PreH35 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH36 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH37 : (CopyMaxState original copied n_pre mx_5 )) (PreH38 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH39 : (Permutation copied sorted )) (PreH40 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH41 : (DivisorScanState sorted d i_2 present count l )) (PreH42 : (z < 2)) (PreH43 : (a_5 <> 0)) (PreH44 : (n_pre = (Zlength (original)))) (PreH45 : ((Zlength (copied)) = n_pre)) (PreH46 : ((Zlength (sorted)) = n_pre)) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : (1 <= mx_4)) (PreH50 : (mx_4 <= 1000000000)) (PreH51 : (all_3 = mx_4)) (PreH52 : (1 <= q_2)) (PreH53 : (q_2 <= 31623)) (PreH54 : ((q_2 * q_2 ) <= mx_4)) (PreH55 : ((mx_4 % ( q_2 ) ) = 0)) (PreH56 : (0 <= z)) (PreH57 : (z <= 2)) (PreH58 : (0 <= ans_2)) (PreH59 : (ans_2 <= n_pre)) (PreH60 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH61 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH62 : (CopyMaxState original copied n_pre mx_4 )) (PreH63 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH64 : (Permutation copied sorted )) (PreH65 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH66 : ((mx_3 % ( q ) ) = 0)) (PreH67 : ((q * q ) <= mx_3)) (PreH68 : (a_4 <> 0)) (PreH69 : (n_pre = (Zlength (original)))) (PreH70 : ((Zlength (copied)) = n_pre)) (PreH71 : ((Zlength (sorted)) = n_pre)) (PreH72 : (1 <= n_pre)) (PreH73 : (n_pre <= 2000)) (PreH74 : (1 <= mx_3)) (PreH75 : (mx_3 <= 1000000000)) (PreH76 : (all_2 = mx_3)) (PreH77 : (1 <= q)) (PreH78 : (q <= 31624)) (PreH79 : (0 <= ans)) (PreH80 : (ans <= n_pre)) (PreH81 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH82 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH83 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH84 : (CopyMaxState original copied n_pre mx_3 )) (PreH85 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH86 : (Permutation copied sorted )) (PreH87 : (DivisorBestState original mx_3 q 0 ans )) (PreH88 : (a_3 <> 0)) (PreH89 : (n_pre = (Zlength (original)))) (PreH90 : ((Zlength (copied)) = n_pre)) (PreH91 : ((Zlength (sorted)) = n_pre)) (PreH92 : (1 <= n_pre)) (PreH93 : (n_pre <= 2000)) (PreH94 : (1 <= all)) (PreH95 : (all <= 1000000000)) (PreH96 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH97 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH98 : (CopyMaxState original copied n_pre all )) (PreH99 : (LcmPrefixState copied n_pre all all )) (PreH100 : (Permutation copied sorted )) (PreH101 : (Permutation copied sorted )) (PreH102 : ((Zlength (sorted)) = n_pre)) (PreH103 : (all = mx_2)) (PreH104 : (i >= n_pre)) (PreH105 : (a_3 <> 0)) (PreH106 : (n_pre = (Zlength (original)))) (PreH107 : ((Zlength (copied)) = n_pre)) (PreH108 : (1 <= n_pre)) (PreH109 : (n_pre <= 2000)) (PreH110 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH111 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH112 : (1 <= mx_2)) (PreH113 : (mx_2 <= 1000000000)) (PreH114 : (0 <= i)) (PreH115 : (i <= n_pre)) (PreH116 : (1 <= all)) (PreH117 : (all <= (mx_2 + 1 ))) (PreH118 : (CopyMaxState original copied n_pre mx_2 )) (PreH119 : (LcmPrefixState copied i mx_2 all )) (PreH120 : (finished_i >= n_pre)) (PreH121 : (a_2 <> 0)) (PreH122 : (n_pre = (Zlength (original)))) (PreH123 : (1 <= n_pre)) (PreH124 : (n_pre <= 2000)) (PreH125 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH126 : (0 <= finished_i)) (PreH127 : (finished_i <= n_pre)) (PreH128 : (0 <= mx)) (PreH129 : (mx <= 1000000000)) (PreH130 : (CopyMaxState original copied finished_i mx )) (PreH131 : (retval <> 0)) (PreH132 : (original = a)) (PreH133 : (n_pre = (Zlength (original)))) (PreH134 : (1 <= n_pre)) (PreH135 : (n_pre <= 2000)) (PreH136 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorScanState sorted d (i_2 + 1 ) 1 (count + 1 ) retval_2 ) ”
  &&  emp
).

Definition solver_entail_wit_11_1_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (d + 1 ))) (PreH3 : (LcmCapValue l (Znth i_2 sorted 0) d retval_2 )) (PreH4 : ((d % ( (Znth i_2 sorted 0) ) ) = 0)) (PreH5 : ((Znth i_2 sorted 0) = d)) (PreH6 : (i_2 < n_pre)) (PreH7 : (a_6 <> 0)) (PreH8 : (n_pre = (Zlength (original)))) (PreH9 : ((Zlength (copied)) = n_pre)) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2000)) (PreH13 : (1 <= mx_5)) (PreH14 : (mx_5 <= 1000000000)) (PreH15 : (all_4 = mx_5)) (PreH16 : (1 <= q_3)) (PreH17 : (q_3 <= 31623)) (PreH18 : ((q_3 * q_3 ) <= mx_5)) (PreH19 : ((mx_5 % ( q_3 ) ) = 0)) (PreH20 : (0 <= z_2)) (PreH21 : (z_2 < 2)) (PreH22 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH23 : (1 <= d)) (PreH24 : (d <= mx_5)) (PreH25 : (0 <= ans_3)) (PreH26 : (ans_3 <= n_pre)) (PreH27 : (0 <= i_2)) (PreH28 : (i_2 <= n_pre)) (PreH29 : (0 <= present)) (PreH30 : (present <= 1)) (PreH31 : (0 <= count)) (PreH32 : (count <= i_2)) (PreH33 : (1 <= l)) (PreH34 : (l <= (d + 1 ))) (PreH35 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH36 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH37 : (CopyMaxState original copied n_pre mx_5 )) (PreH38 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH39 : (Permutation copied sorted )) (PreH40 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH41 : (DivisorScanState sorted d i_2 present count l )) (PreH42 : (z < 2)) (PreH43 : (a_5 <> 0)) (PreH44 : (n_pre = (Zlength (original)))) (PreH45 : ((Zlength (copied)) = n_pre)) (PreH46 : ((Zlength (sorted)) = n_pre)) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : (1 <= mx_4)) (PreH50 : (mx_4 <= 1000000000)) (PreH51 : (all_3 = mx_4)) (PreH52 : (1 <= q_2)) (PreH53 : (q_2 <= 31623)) (PreH54 : ((q_2 * q_2 ) <= mx_4)) (PreH55 : ((mx_4 % ( q_2 ) ) = 0)) (PreH56 : (0 <= z)) (PreH57 : (z <= 2)) (PreH58 : (0 <= ans_2)) (PreH59 : (ans_2 <= n_pre)) (PreH60 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH61 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH62 : (CopyMaxState original copied n_pre mx_4 )) (PreH63 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH64 : (Permutation copied sorted )) (PreH65 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH66 : ((mx_3 % ( q ) ) = 0)) (PreH67 : ((q * q ) <= mx_3)) (PreH68 : (a_4 <> 0)) (PreH69 : (n_pre = (Zlength (original)))) (PreH70 : ((Zlength (copied)) = n_pre)) (PreH71 : ((Zlength (sorted)) = n_pre)) (PreH72 : (1 <= n_pre)) (PreH73 : (n_pre <= 2000)) (PreH74 : (1 <= mx_3)) (PreH75 : (mx_3 <= 1000000000)) (PreH76 : (all_2 = mx_3)) (PreH77 : (1 <= q)) (PreH78 : (q <= 31624)) (PreH79 : (0 <= ans)) (PreH80 : (ans <= n_pre)) (PreH81 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH82 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH83 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH84 : (CopyMaxState original copied n_pre mx_3 )) (PreH85 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH86 : (Permutation copied sorted )) (PreH87 : (DivisorBestState original mx_3 q 0 ans )) (PreH88 : (a_3 <> 0)) (PreH89 : (n_pre = (Zlength (original)))) (PreH90 : ((Zlength (copied)) = n_pre)) (PreH91 : ((Zlength (sorted)) = n_pre)) (PreH92 : (1 <= n_pre)) (PreH93 : (n_pre <= 2000)) (PreH94 : (1 <= all)) (PreH95 : (all <= 1000000000)) (PreH96 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH97 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH98 : (CopyMaxState original copied n_pre all )) (PreH99 : (LcmPrefixState copied n_pre all all )) (PreH100 : (Permutation copied sorted )) (PreH101 : (Permutation copied sorted )) (PreH102 : ((Zlength (sorted)) = n_pre)) (PreH103 : (all = mx_2)) (PreH104 : (i >= n_pre)) (PreH105 : (a_3 <> 0)) (PreH106 : (n_pre = (Zlength (original)))) (PreH107 : ((Zlength (copied)) = n_pre)) (PreH108 : (1 <= n_pre)) (PreH109 : (n_pre <= 2000)) (PreH110 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH111 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH112 : (1 <= mx_2)) (PreH113 : (mx_2 <= 1000000000)) (PreH114 : (0 <= i)) (PreH115 : (i <= n_pre)) (PreH116 : (1 <= all)) (PreH117 : (all <= (mx_2 + 1 ))) (PreH118 : (CopyMaxState original copied n_pre mx_2 )) (PreH119 : (LcmPrefixState copied i mx_2 all )) (PreH120 : (finished_i >= n_pre)) (PreH121 : (a_2 <> 0)) (PreH122 : (n_pre = (Zlength (original)))) (PreH123 : (1 <= n_pre)) (PreH124 : (n_pre <= 2000)) (PreH125 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH126 : (0 <= finished_i)) (PreH127 : (finished_i <= n_pre)) (PreH128 : (0 <= mx)) (PreH129 : (mx <= 1000000000)) (PreH130 : (CopyMaxState original copied finished_i mx )) (PreH131 : (retval <> 0)) (PreH132 : (original = a)) (PreH133 : (n_pre = (Zlength (original)))) (PreH134 : (1 <= n_pre)) (PreH135 : (n_pre <= 2000)) (PreH136 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorScanState sorted d (i_2 + 1 ) 1 (count + 1 ) retval_2 )
.

Definition solver_entail_wit_11_2 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (d + 1 ))) (PreH3 : (LcmCapValue l (Znth i_2 sorted 0) d retval_2 )) (PreH4 : ((d % ( (Znth i_2 sorted 0) ) ) = 0)) (PreH5 : ((Znth i_2 sorted 0) <> d)) (PreH6 : (i_2 < n_pre)) (PreH7 : (a_6 <> 0)) (PreH8 : (n_pre = (Zlength (original)))) (PreH9 : ((Zlength (copied)) = n_pre)) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2000)) (PreH13 : (1 <= mx_5)) (PreH14 : (mx_5 <= 1000000000)) (PreH15 : (all_4 = mx_5)) (PreH16 : (1 <= q_3)) (PreH17 : (q_3 <= 31623)) (PreH18 : ((q_3 * q_3 ) <= mx_5)) (PreH19 : ((mx_5 % ( q_3 ) ) = 0)) (PreH20 : (0 <= z_2)) (PreH21 : (z_2 < 2)) (PreH22 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH23 : (1 <= d)) (PreH24 : (d <= mx_5)) (PreH25 : (0 <= ans_3)) (PreH26 : (ans_3 <= n_pre)) (PreH27 : (0 <= i_2)) (PreH28 : (i_2 <= n_pre)) (PreH29 : (0 <= present)) (PreH30 : (present <= 1)) (PreH31 : (0 <= count)) (PreH32 : (count <= i_2)) (PreH33 : (1 <= l)) (PreH34 : (l <= (d + 1 ))) (PreH35 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH36 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH37 : (CopyMaxState original copied n_pre mx_5 )) (PreH38 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH39 : (Permutation copied sorted )) (PreH40 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH41 : (DivisorScanState sorted d i_2 present count l )) (PreH42 : (z < 2)) (PreH43 : (a_5 <> 0)) (PreH44 : (n_pre = (Zlength (original)))) (PreH45 : ((Zlength (copied)) = n_pre)) (PreH46 : ((Zlength (sorted)) = n_pre)) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : (1 <= mx_4)) (PreH50 : (mx_4 <= 1000000000)) (PreH51 : (all_3 = mx_4)) (PreH52 : (1 <= q_2)) (PreH53 : (q_2 <= 31623)) (PreH54 : ((q_2 * q_2 ) <= mx_4)) (PreH55 : ((mx_4 % ( q_2 ) ) = 0)) (PreH56 : (0 <= z)) (PreH57 : (z <= 2)) (PreH58 : (0 <= ans_2)) (PreH59 : (ans_2 <= n_pre)) (PreH60 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH61 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH62 : (CopyMaxState original copied n_pre mx_4 )) (PreH63 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH64 : (Permutation copied sorted )) (PreH65 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH66 : ((mx_3 % ( q ) ) = 0)) (PreH67 : ((q * q ) <= mx_3)) (PreH68 : (a_4 <> 0)) (PreH69 : (n_pre = (Zlength (original)))) (PreH70 : ((Zlength (copied)) = n_pre)) (PreH71 : ((Zlength (sorted)) = n_pre)) (PreH72 : (1 <= n_pre)) (PreH73 : (n_pre <= 2000)) (PreH74 : (1 <= mx_3)) (PreH75 : (mx_3 <= 1000000000)) (PreH76 : (all_2 = mx_3)) (PreH77 : (1 <= q)) (PreH78 : (q <= 31624)) (PreH79 : (0 <= ans)) (PreH80 : (ans <= n_pre)) (PreH81 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH82 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH83 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH84 : (CopyMaxState original copied n_pre mx_3 )) (PreH85 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH86 : (Permutation copied sorted )) (PreH87 : (DivisorBestState original mx_3 q 0 ans )) (PreH88 : (a_3 <> 0)) (PreH89 : (n_pre = (Zlength (original)))) (PreH90 : ((Zlength (copied)) = n_pre)) (PreH91 : ((Zlength (sorted)) = n_pre)) (PreH92 : (1 <= n_pre)) (PreH93 : (n_pre <= 2000)) (PreH94 : (1 <= all)) (PreH95 : (all <= 1000000000)) (PreH96 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH97 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH98 : (CopyMaxState original copied n_pre all )) (PreH99 : (LcmPrefixState copied n_pre all all )) (PreH100 : (Permutation copied sorted )) (PreH101 : (Permutation copied sorted )) (PreH102 : ((Zlength (sorted)) = n_pre)) (PreH103 : (all = mx_2)) (PreH104 : (i >= n_pre)) (PreH105 : (a_3 <> 0)) (PreH106 : (n_pre = (Zlength (original)))) (PreH107 : ((Zlength (copied)) = n_pre)) (PreH108 : (1 <= n_pre)) (PreH109 : (n_pre <= 2000)) (PreH110 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH111 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH112 : (1 <= mx_2)) (PreH113 : (mx_2 <= 1000000000)) (PreH114 : (0 <= i)) (PreH115 : (i <= n_pre)) (PreH116 : (1 <= all)) (PreH117 : (all <= (mx_2 + 1 ))) (PreH118 : (CopyMaxState original copied n_pre mx_2 )) (PreH119 : (LcmPrefixState copied i mx_2 all )) (PreH120 : (finished_i >= n_pre)) (PreH121 : (a_2 <> 0)) (PreH122 : (n_pre = (Zlength (original)))) (PreH123 : (1 <= n_pre)) (PreH124 : (n_pre <= 2000)) (PreH125 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH126 : (0 <= finished_i)) (PreH127 : (finished_i <= n_pre)) (PreH128 : (0 <= mx)) (PreH129 : (mx <= 1000000000)) (PreH130 : (CopyMaxState original copied finished_i mx )) (PreH131 : (retval <> 0)) (PreH132 : (original = a)) (PreH133 : (n_pre = (Zlength (original)))) (PreH134 : (1 <= n_pre)) (PreH135 : (n_pre <= 2000)) (PreH136 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ (0 <= present) ” 
  &&  “ (present <= 1) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i_2 + 1 )) ” 
  &&  “ (1 <= retval_2) ” 
  &&  “ (retval_2 <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d (i_2 + 1 ) present (count + 1 ) retval_2 ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (d + 1 ))) (PreH3 : (LcmCapValue l (Znth i_2 sorted 0) d retval_2 )) (PreH4 : ((d % ( (Znth i_2 sorted 0) ) ) = 0)) (PreH5 : ((Znth i_2 sorted 0) <> d)) (PreH6 : (i_2 < n_pre)) (PreH7 : (a_6 <> 0)) (PreH8 : (n_pre = (Zlength (original)))) (PreH9 : ((Zlength (copied)) = n_pre)) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2000)) (PreH13 : (1 <= mx_5)) (PreH14 : (mx_5 <= 1000000000)) (PreH15 : (all_4 = mx_5)) (PreH16 : (1 <= q_3)) (PreH17 : (q_3 <= 31623)) (PreH18 : ((q_3 * q_3 ) <= mx_5)) (PreH19 : ((mx_5 % ( q_3 ) ) = 0)) (PreH20 : (0 <= z_2)) (PreH21 : (z_2 < 2)) (PreH22 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH23 : (1 <= d)) (PreH24 : (d <= mx_5)) (PreH25 : (0 <= ans_3)) (PreH26 : (ans_3 <= n_pre)) (PreH27 : (0 <= i_2)) (PreH28 : (i_2 <= n_pre)) (PreH29 : (0 <= present)) (PreH30 : (present <= 1)) (PreH31 : (0 <= count)) (PreH32 : (count <= i_2)) (PreH33 : (1 <= l)) (PreH34 : (l <= (d + 1 ))) (PreH35 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH36 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH37 : (CopyMaxState original copied n_pre mx_5 )) (PreH38 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH39 : (Permutation copied sorted )) (PreH40 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH41 : (DivisorScanState sorted d i_2 present count l )) (PreH42 : (z < 2)) (PreH43 : (a_5 <> 0)) (PreH44 : (n_pre = (Zlength (original)))) (PreH45 : ((Zlength (copied)) = n_pre)) (PreH46 : ((Zlength (sorted)) = n_pre)) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : (1 <= mx_4)) (PreH50 : (mx_4 <= 1000000000)) (PreH51 : (all_3 = mx_4)) (PreH52 : (1 <= q_2)) (PreH53 : (q_2 <= 31623)) (PreH54 : ((q_2 * q_2 ) <= mx_4)) (PreH55 : ((mx_4 % ( q_2 ) ) = 0)) (PreH56 : (0 <= z)) (PreH57 : (z <= 2)) (PreH58 : (0 <= ans_2)) (PreH59 : (ans_2 <= n_pre)) (PreH60 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH61 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH62 : (CopyMaxState original copied n_pre mx_4 )) (PreH63 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH64 : (Permutation copied sorted )) (PreH65 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH66 : ((mx_3 % ( q ) ) = 0)) (PreH67 : ((q * q ) <= mx_3)) (PreH68 : (a_4 <> 0)) (PreH69 : (n_pre = (Zlength (original)))) (PreH70 : ((Zlength (copied)) = n_pre)) (PreH71 : ((Zlength (sorted)) = n_pre)) (PreH72 : (1 <= n_pre)) (PreH73 : (n_pre <= 2000)) (PreH74 : (1 <= mx_3)) (PreH75 : (mx_3 <= 1000000000)) (PreH76 : (all_2 = mx_3)) (PreH77 : (1 <= q)) (PreH78 : (q <= 31624)) (PreH79 : (0 <= ans)) (PreH80 : (ans <= n_pre)) (PreH81 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH82 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH83 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH84 : (CopyMaxState original copied n_pre mx_3 )) (PreH85 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH86 : (Permutation copied sorted )) (PreH87 : (DivisorBestState original mx_3 q 0 ans )) (PreH88 : (a_3 <> 0)) (PreH89 : (n_pre = (Zlength (original)))) (PreH90 : ((Zlength (copied)) = n_pre)) (PreH91 : ((Zlength (sorted)) = n_pre)) (PreH92 : (1 <= n_pre)) (PreH93 : (n_pre <= 2000)) (PreH94 : (1 <= all)) (PreH95 : (all <= 1000000000)) (PreH96 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH97 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH98 : (CopyMaxState original copied n_pre all )) (PreH99 : (LcmPrefixState copied n_pre all all )) (PreH100 : (Permutation copied sorted )) (PreH101 : (Permutation copied sorted )) (PreH102 : ((Zlength (sorted)) = n_pre)) (PreH103 : (all = mx_2)) (PreH104 : (i >= n_pre)) (PreH105 : (a_3 <> 0)) (PreH106 : (n_pre = (Zlength (original)))) (PreH107 : ((Zlength (copied)) = n_pre)) (PreH108 : (1 <= n_pre)) (PreH109 : (n_pre <= 2000)) (PreH110 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH111 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH112 : (1 <= mx_2)) (PreH113 : (mx_2 <= 1000000000)) (PreH114 : (0 <= i)) (PreH115 : (i <= n_pre)) (PreH116 : (1 <= all)) (PreH117 : (all <= (mx_2 + 1 ))) (PreH118 : (CopyMaxState original copied n_pre mx_2 )) (PreH119 : (LcmPrefixState copied i mx_2 all )) (PreH120 : (finished_i >= n_pre)) (PreH121 : (a_2 <> 0)) (PreH122 : (n_pre = (Zlength (original)))) (PreH123 : (1 <= n_pre)) (PreH124 : (n_pre <= 2000)) (PreH125 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH126 : (0 <= finished_i)) (PreH127 : (finished_i <= n_pre)) (PreH128 : (0 <= mx)) (PreH129 : (mx <= 1000000000)) (PreH130 : (CopyMaxState original copied finished_i mx )) (PreH131 : (retval <> 0)) (PreH132 : (original = a)) (PreH133 : (n_pre = (Zlength (original)))) (PreH134 : (1 <= n_pre)) (PreH135 : (n_pre <= 2000)) (PreH136 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorScanState sorted d (i_2 + 1 ) present (count + 1 ) retval_2 ) ”
  &&  emp
).

Definition solver_entail_wit_11_2_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (retval_2: Z) (PreH1 : (1 <= retval_2)) (PreH2 : (retval_2 <= (d + 1 ))) (PreH3 : (LcmCapValue l (Znth i_2 sorted 0) d retval_2 )) (PreH4 : ((d % ( (Znth i_2 sorted 0) ) ) = 0)) (PreH5 : ((Znth i_2 sorted 0) <> d)) (PreH6 : (i_2 < n_pre)) (PreH7 : (a_6 <> 0)) (PreH8 : (n_pre = (Zlength (original)))) (PreH9 : ((Zlength (copied)) = n_pre)) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2000)) (PreH13 : (1 <= mx_5)) (PreH14 : (mx_5 <= 1000000000)) (PreH15 : (all_4 = mx_5)) (PreH16 : (1 <= q_3)) (PreH17 : (q_3 <= 31623)) (PreH18 : ((q_3 * q_3 ) <= mx_5)) (PreH19 : ((mx_5 % ( q_3 ) ) = 0)) (PreH20 : (0 <= z_2)) (PreH21 : (z_2 < 2)) (PreH22 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH23 : (1 <= d)) (PreH24 : (d <= mx_5)) (PreH25 : (0 <= ans_3)) (PreH26 : (ans_3 <= n_pre)) (PreH27 : (0 <= i_2)) (PreH28 : (i_2 <= n_pre)) (PreH29 : (0 <= present)) (PreH30 : (present <= 1)) (PreH31 : (0 <= count)) (PreH32 : (count <= i_2)) (PreH33 : (1 <= l)) (PreH34 : (l <= (d + 1 ))) (PreH35 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH36 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH37 : (CopyMaxState original copied n_pre mx_5 )) (PreH38 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH39 : (Permutation copied sorted )) (PreH40 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH41 : (DivisorScanState sorted d i_2 present count l )) (PreH42 : (z < 2)) (PreH43 : (a_5 <> 0)) (PreH44 : (n_pre = (Zlength (original)))) (PreH45 : ((Zlength (copied)) = n_pre)) (PreH46 : ((Zlength (sorted)) = n_pre)) (PreH47 : (1 <= n_pre)) (PreH48 : (n_pre <= 2000)) (PreH49 : (1 <= mx_4)) (PreH50 : (mx_4 <= 1000000000)) (PreH51 : (all_3 = mx_4)) (PreH52 : (1 <= q_2)) (PreH53 : (q_2 <= 31623)) (PreH54 : ((q_2 * q_2 ) <= mx_4)) (PreH55 : ((mx_4 % ( q_2 ) ) = 0)) (PreH56 : (0 <= z)) (PreH57 : (z <= 2)) (PreH58 : (0 <= ans_2)) (PreH59 : (ans_2 <= n_pre)) (PreH60 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH61 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH62 : (CopyMaxState original copied n_pre mx_4 )) (PreH63 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH64 : (Permutation copied sorted )) (PreH65 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH66 : ((mx_3 % ( q ) ) = 0)) (PreH67 : ((q * q ) <= mx_3)) (PreH68 : (a_4 <> 0)) (PreH69 : (n_pre = (Zlength (original)))) (PreH70 : ((Zlength (copied)) = n_pre)) (PreH71 : ((Zlength (sorted)) = n_pre)) (PreH72 : (1 <= n_pre)) (PreH73 : (n_pre <= 2000)) (PreH74 : (1 <= mx_3)) (PreH75 : (mx_3 <= 1000000000)) (PreH76 : (all_2 = mx_3)) (PreH77 : (1 <= q)) (PreH78 : (q <= 31624)) (PreH79 : (0 <= ans)) (PreH80 : (ans <= n_pre)) (PreH81 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH82 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH83 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH84 : (CopyMaxState original copied n_pre mx_3 )) (PreH85 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH86 : (Permutation copied sorted )) (PreH87 : (DivisorBestState original mx_3 q 0 ans )) (PreH88 : (a_3 <> 0)) (PreH89 : (n_pre = (Zlength (original)))) (PreH90 : ((Zlength (copied)) = n_pre)) (PreH91 : ((Zlength (sorted)) = n_pre)) (PreH92 : (1 <= n_pre)) (PreH93 : (n_pre <= 2000)) (PreH94 : (1 <= all)) (PreH95 : (all <= 1000000000)) (PreH96 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH97 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH98 : (CopyMaxState original copied n_pre all )) (PreH99 : (LcmPrefixState copied n_pre all all )) (PreH100 : (Permutation copied sorted )) (PreH101 : (Permutation copied sorted )) (PreH102 : ((Zlength (sorted)) = n_pre)) (PreH103 : (all = mx_2)) (PreH104 : (i >= n_pre)) (PreH105 : (a_3 <> 0)) (PreH106 : (n_pre = (Zlength (original)))) (PreH107 : ((Zlength (copied)) = n_pre)) (PreH108 : (1 <= n_pre)) (PreH109 : (n_pre <= 2000)) (PreH110 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH111 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH112 : (1 <= mx_2)) (PreH113 : (mx_2 <= 1000000000)) (PreH114 : (0 <= i)) (PreH115 : (i <= n_pre)) (PreH116 : (1 <= all)) (PreH117 : (all <= (mx_2 + 1 ))) (PreH118 : (CopyMaxState original copied n_pre mx_2 )) (PreH119 : (LcmPrefixState copied i mx_2 all )) (PreH120 : (finished_i >= n_pre)) (PreH121 : (a_2 <> 0)) (PreH122 : (n_pre = (Zlength (original)))) (PreH123 : (1 <= n_pre)) (PreH124 : (n_pre <= 2000)) (PreH125 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH126 : (0 <= finished_i)) (PreH127 : (finished_i <= n_pre)) (PreH128 : (0 <= mx)) (PreH129 : (mx <= 1000000000)) (PreH130 : (CopyMaxState original copied finished_i mx )) (PreH131 : (retval <> 0)) (PreH132 : (original = a)) (PreH133 : (n_pre = (Zlength (original)))) (PreH134 : (1 <= n_pre)) (PreH135 : (n_pre <= 2000)) (PreH136 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorScanState sorted d (i_2 + 1 ) present (count + 1 ) retval_2 )
.

Definition solver_entail_wit_11_3 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i_2 sorted 0) ) ) <> 0)) (PreH2 : ((Znth i_2 sorted 0) = d)) (PreH3 : (i_2 < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i_2 + 1 )) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d (i_2 + 1 ) 1 count l ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i_2 sorted 0) ) ) <> 0)) (PreH2 : ((Znth i_2 sorted 0) = d)) (PreH3 : (i_2 < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorScanState sorted d (i_2 + 1 ) 1 count l ) ”
  &&  emp
).

Definition solver_entail_wit_11_3_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i_2 sorted 0) ) ) <> 0)) (PreH2 : ((Znth i_2 sorted 0) = d)) (PreH3 : (i_2 < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorScanState sorted d (i_2 + 1 ) 1 count l )
.

Definition solver_entail_wit_11_4 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i_2 sorted 0) ) ) <> 0)) (PreH2 : ((Znth i_2 sorted 0) <> d)) (PreH3 : (i_2 < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ (0 <= present) ” 
  &&  “ (present <= 1) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i_2 + 1 )) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d (i_2 + 1 ) present count l ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i_2 sorted 0) ) ) <> 0)) (PreH2 : ((Znth i_2 sorted 0) <> d)) (PreH3 : (i_2 < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorScanState sorted d (i_2 + 1 ) present count l ) ”
  &&  emp
).

Definition solver_entail_wit_11_4_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i_2 sorted 0) ) ) <> 0)) (PreH2 : ((Znth i_2 sorted 0) <> d)) (PreH3 : (i_2 < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorScanState sorted d (i_2 + 1 ) present count l )
.

Definition solver_entail_wit_12_1 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (count > ans_3)) (PreH2 : (l = d)) (PreH3 : (present = 0)) (PreH4 : (i_2 >= n_pre)) (PreH5 : (a_5 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (1 <= mx_4)) (PreH12 : (mx_4 <= 1000000000)) (PreH13 : (all_3 = mx_4)) (PreH14 : (1 <= q_2)) (PreH15 : (q_2 <= 31623)) (PreH16 : ((q_2 * q_2 ) <= mx_4)) (PreH17 : ((mx_4 % ( q_2 ) ) = 0)) (PreH18 : (0 <= z)) (PreH19 : (z < 2)) (PreH20 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH21 : (1 <= d)) (PreH22 : (d <= mx_4)) (PreH23 : (0 <= ans_3)) (PreH24 : (ans_3 <= n_pre)) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 <= n_pre)) (PreH27 : (0 <= present)) (PreH28 : (present <= 1)) (PreH29 : (0 <= count)) (PreH30 : (count <= i_2)) (PreH31 : (1 <= l)) (PreH32 : (l <= (d + 1 ))) (PreH33 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH34 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH35 : (CopyMaxState original copied n_pre mx_4 )) (PreH36 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH37 : (Permutation copied sorted )) (PreH38 : (DivisorBestState original mx_4 q_2 z ans_3 )) (PreH39 : (DivisorScanState sorted d i_2 present count l )) (PreH40 : (z_2 < 2)) (PreH41 : (a_6 <> 0)) (PreH42 : (n_pre = (Zlength (original)))) (PreH43 : ((Zlength (copied)) = n_pre)) (PreH44 : ((Zlength (sorted)) = n_pre)) (PreH45 : (1 <= n_pre)) (PreH46 : (n_pre <= 2000)) (PreH47 : (1 <= mx_5)) (PreH48 : (mx_5 <= 1000000000)) (PreH49 : (all_4 = mx_5)) (PreH50 : (1 <= q_3)) (PreH51 : (q_3 <= 31623)) (PreH52 : ((q_3 * q_3 ) <= mx_5)) (PreH53 : ((mx_5 % ( q_3 ) ) = 0)) (PreH54 : (0 <= z_2)) (PreH55 : (z_2 <= 2)) (PreH56 : (0 <= ans_2)) (PreH57 : (ans_2 <= n_pre)) (PreH58 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH59 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH60 : (CopyMaxState original copied n_pre mx_5 )) (PreH61 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH62 : (Permutation copied sorted )) (PreH63 : (DivisorBestState original mx_5 q_3 z_2 ans_2 )) (PreH64 : ((mx_3 % ( q ) ) = 0)) (PreH65 : ((q * q ) <= mx_3)) (PreH66 : (a_4 <> 0)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : ((Zlength (copied)) = n_pre)) (PreH69 : ((Zlength (sorted)) = n_pre)) (PreH70 : (1 <= n_pre)) (PreH71 : (n_pre <= 2000)) (PreH72 : (1 <= mx_3)) (PreH73 : (mx_3 <= 1000000000)) (PreH74 : (all_2 = mx_3)) (PreH75 : (1 <= q)) (PreH76 : (q <= 31624)) (PreH77 : (0 <= ans)) (PreH78 : (ans <= n_pre)) (PreH79 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH80 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH81 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH82 : (CopyMaxState original copied n_pre mx_3 )) (PreH83 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH84 : (Permutation copied sorted )) (PreH85 : (DivisorBestState original mx_3 q 0 ans )) (PreH86 : (a_3 <> 0)) (PreH87 : (n_pre = (Zlength (original)))) (PreH88 : ((Zlength (copied)) = n_pre)) (PreH89 : ((Zlength (sorted)) = n_pre)) (PreH90 : (1 <= n_pre)) (PreH91 : (n_pre <= 2000)) (PreH92 : (1 <= all)) (PreH93 : (all <= 1000000000)) (PreH94 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH95 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH96 : (CopyMaxState original copied n_pre all )) (PreH97 : (LcmPrefixState copied n_pre all all )) (PreH98 : (Permutation copied sorted )) (PreH99 : (Permutation copied sorted )) (PreH100 : ((Zlength (sorted)) = n_pre)) (PreH101 : (all = mx_2)) (PreH102 : (i >= n_pre)) (PreH103 : (a_3 <> 0)) (PreH104 : (n_pre = (Zlength (original)))) (PreH105 : ((Zlength (copied)) = n_pre)) (PreH106 : (1 <= n_pre)) (PreH107 : (n_pre <= 2000)) (PreH108 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH109 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH110 : (1 <= mx_2)) (PreH111 : (mx_2 <= 1000000000)) (PreH112 : (0 <= i)) (PreH113 : (i <= n_pre)) (PreH114 : (1 <= all)) (PreH115 : (all <= (mx_2 + 1 ))) (PreH116 : (CopyMaxState original copied n_pre mx_2 )) (PreH117 : (LcmPrefixState copied i mx_2 all )) (PreH118 : (finished_i >= n_pre)) (PreH119 : (a_2 <> 0)) (PreH120 : (n_pre = (Zlength (original)))) (PreH121 : (1 <= n_pre)) (PreH122 : (n_pre <= 2000)) (PreH123 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH124 : (0 <= finished_i)) (PreH125 : (finished_i <= n_pre)) (PreH126 : (0 <= mx)) (PreH127 : (mx <= 1000000000)) (PreH128 : (CopyMaxState original copied finished_i mx )) (PreH129 : (retval <> 0)) (PreH130 : (original = a)) (PreH131 : (n_pre = (Zlength (original)))) (PreH132 : (1 <= n_pre)) (PreH133 : (n_pre <= 2000)) (PreH134 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
|--
  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= (z + 1 )) ” 
  &&  “ ((z + 1 ) <= 2) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 (z + 1 ) count ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (count > ans_3)) (PreH2 : (l = d)) (PreH3 : (present = 0)) (PreH4 : (i_2 >= n_pre)) (PreH5 : (a_5 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (1 <= mx_4)) (PreH12 : (mx_4 <= 1000000000)) (PreH13 : (all_3 = mx_4)) (PreH14 : (1 <= q_2)) (PreH15 : (q_2 <= 31623)) (PreH16 : ((q_2 * q_2 ) <= mx_4)) (PreH17 : ((mx_4 % ( q_2 ) ) = 0)) (PreH18 : (0 <= z)) (PreH19 : (z < 2)) (PreH20 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH21 : (1 <= d)) (PreH22 : (d <= mx_4)) (PreH23 : (0 <= ans_3)) (PreH24 : (ans_3 <= n_pre)) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 <= n_pre)) (PreH27 : (0 <= present)) (PreH28 : (present <= 1)) (PreH29 : (0 <= count)) (PreH30 : (count <= i_2)) (PreH31 : (1 <= l)) (PreH32 : (l <= (d + 1 ))) (PreH33 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH34 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH35 : (CopyMaxState original copied n_pre mx_4 )) (PreH36 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH37 : (Permutation copied sorted )) (PreH38 : (DivisorBestState original mx_4 q_2 z ans_3 )) (PreH39 : (DivisorScanState sorted d i_2 present count l )) (PreH40 : (z_2 < 2)) (PreH41 : (a_6 <> 0)) (PreH42 : (n_pre = (Zlength (original)))) (PreH43 : ((Zlength (copied)) = n_pre)) (PreH44 : ((Zlength (sorted)) = n_pre)) (PreH45 : (1 <= n_pre)) (PreH46 : (n_pre <= 2000)) (PreH47 : (1 <= mx_5)) (PreH48 : (mx_5 <= 1000000000)) (PreH49 : (all_4 = mx_5)) (PreH50 : (1 <= q_3)) (PreH51 : (q_3 <= 31623)) (PreH52 : ((q_3 * q_3 ) <= mx_5)) (PreH53 : ((mx_5 % ( q_3 ) ) = 0)) (PreH54 : (0 <= z_2)) (PreH55 : (z_2 <= 2)) (PreH56 : (0 <= ans_2)) (PreH57 : (ans_2 <= n_pre)) (PreH58 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH59 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH60 : (CopyMaxState original copied n_pre mx_5 )) (PreH61 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH62 : (Permutation copied sorted )) (PreH63 : (DivisorBestState original mx_5 q_3 z_2 ans_2 )) (PreH64 : ((mx_3 % ( q ) ) = 0)) (PreH65 : ((q * q ) <= mx_3)) (PreH66 : (a_4 <> 0)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : ((Zlength (copied)) = n_pre)) (PreH69 : ((Zlength (sorted)) = n_pre)) (PreH70 : (1 <= n_pre)) (PreH71 : (n_pre <= 2000)) (PreH72 : (1 <= mx_3)) (PreH73 : (mx_3 <= 1000000000)) (PreH74 : (all_2 = mx_3)) (PreH75 : (1 <= q)) (PreH76 : (q <= 31624)) (PreH77 : (0 <= ans)) (PreH78 : (ans <= n_pre)) (PreH79 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH80 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH81 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH82 : (CopyMaxState original copied n_pre mx_3 )) (PreH83 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH84 : (Permutation copied sorted )) (PreH85 : (DivisorBestState original mx_3 q 0 ans )) (PreH86 : (a_3 <> 0)) (PreH87 : (n_pre = (Zlength (original)))) (PreH88 : ((Zlength (copied)) = n_pre)) (PreH89 : ((Zlength (sorted)) = n_pre)) (PreH90 : (1 <= n_pre)) (PreH91 : (n_pre <= 2000)) (PreH92 : (1 <= all)) (PreH93 : (all <= 1000000000)) (PreH94 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH95 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH96 : (CopyMaxState original copied n_pre all )) (PreH97 : (LcmPrefixState copied n_pre all all )) (PreH98 : (Permutation copied sorted )) (PreH99 : (Permutation copied sorted )) (PreH100 : ((Zlength (sorted)) = n_pre)) (PreH101 : (all = mx_2)) (PreH102 : (i >= n_pre)) (PreH103 : (a_3 <> 0)) (PreH104 : (n_pre = (Zlength (original)))) (PreH105 : ((Zlength (copied)) = n_pre)) (PreH106 : (1 <= n_pre)) (PreH107 : (n_pre <= 2000)) (PreH108 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH109 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH110 : (1 <= mx_2)) (PreH111 : (mx_2 <= 1000000000)) (PreH112 : (0 <= i)) (PreH113 : (i <= n_pre)) (PreH114 : (1 <= all)) (PreH115 : (all <= (mx_2 + 1 ))) (PreH116 : (CopyMaxState original copied n_pre mx_2 )) (PreH117 : (LcmPrefixState copied i mx_2 all )) (PreH118 : (finished_i >= n_pre)) (PreH119 : (a_2 <> 0)) (PreH120 : (n_pre = (Zlength (original)))) (PreH121 : (1 <= n_pre)) (PreH122 : (n_pre <= 2000)) (PreH123 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH124 : (0 <= finished_i)) (PreH125 : (finished_i <= n_pre)) (PreH126 : (0 <= mx)) (PreH127 : (mx <= 1000000000)) (PreH128 : (CopyMaxState original copied finished_i mx )) (PreH129 : (retval <> 0)) (PreH130 : (original = a)) (PreH131 : (n_pre = (Zlength (original)))) (PreH132 : (1 <= n_pre)) (PreH133 : (n_pre <= 2000)) (PreH134 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorBestState a all_3 q_2 (z + 1 ) count ) ”
  &&  emp
).

Definition solver_entail_wit_12_1_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (count > ans_3)) (PreH2 : (l = d)) (PreH3 : (present = 0)) (PreH4 : (i_2 >= n_pre)) (PreH5 : (a_5 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (1 <= mx_4)) (PreH12 : (mx_4 <= 1000000000)) (PreH13 : (all_3 = mx_4)) (PreH14 : (1 <= q_2)) (PreH15 : (q_2 <= 31623)) (PreH16 : ((q_2 * q_2 ) <= mx_4)) (PreH17 : ((mx_4 % ( q_2 ) ) = 0)) (PreH18 : (0 <= z)) (PreH19 : (z < 2)) (PreH20 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH21 : (1 <= d)) (PreH22 : (d <= mx_4)) (PreH23 : (0 <= ans_3)) (PreH24 : (ans_3 <= n_pre)) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 <= n_pre)) (PreH27 : (0 <= present)) (PreH28 : (present <= 1)) (PreH29 : (0 <= count)) (PreH30 : (count <= i_2)) (PreH31 : (1 <= l)) (PreH32 : (l <= (d + 1 ))) (PreH33 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH34 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH35 : (CopyMaxState original copied n_pre mx_4 )) (PreH36 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH37 : (Permutation copied sorted )) (PreH38 : (DivisorBestState original mx_4 q_2 z ans_3 )) (PreH39 : (DivisorScanState sorted d i_2 present count l )) (PreH40 : (z_2 < 2)) (PreH41 : (a_6 <> 0)) (PreH42 : (n_pre = (Zlength (original)))) (PreH43 : ((Zlength (copied)) = n_pre)) (PreH44 : ((Zlength (sorted)) = n_pre)) (PreH45 : (1 <= n_pre)) (PreH46 : (n_pre <= 2000)) (PreH47 : (1 <= mx_5)) (PreH48 : (mx_5 <= 1000000000)) (PreH49 : (all_4 = mx_5)) (PreH50 : (1 <= q_3)) (PreH51 : (q_3 <= 31623)) (PreH52 : ((q_3 * q_3 ) <= mx_5)) (PreH53 : ((mx_5 % ( q_3 ) ) = 0)) (PreH54 : (0 <= z_2)) (PreH55 : (z_2 <= 2)) (PreH56 : (0 <= ans_2)) (PreH57 : (ans_2 <= n_pre)) (PreH58 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH59 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH60 : (CopyMaxState original copied n_pre mx_5 )) (PreH61 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH62 : (Permutation copied sorted )) (PreH63 : (DivisorBestState original mx_5 q_3 z_2 ans_2 )) (PreH64 : ((mx_3 % ( q ) ) = 0)) (PreH65 : ((q * q ) <= mx_3)) (PreH66 : (a_4 <> 0)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : ((Zlength (copied)) = n_pre)) (PreH69 : ((Zlength (sorted)) = n_pre)) (PreH70 : (1 <= n_pre)) (PreH71 : (n_pre <= 2000)) (PreH72 : (1 <= mx_3)) (PreH73 : (mx_3 <= 1000000000)) (PreH74 : (all_2 = mx_3)) (PreH75 : (1 <= q)) (PreH76 : (q <= 31624)) (PreH77 : (0 <= ans)) (PreH78 : (ans <= n_pre)) (PreH79 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH80 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH81 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH82 : (CopyMaxState original copied n_pre mx_3 )) (PreH83 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH84 : (Permutation copied sorted )) (PreH85 : (DivisorBestState original mx_3 q 0 ans )) (PreH86 : (a_3 <> 0)) (PreH87 : (n_pre = (Zlength (original)))) (PreH88 : ((Zlength (copied)) = n_pre)) (PreH89 : ((Zlength (sorted)) = n_pre)) (PreH90 : (1 <= n_pre)) (PreH91 : (n_pre <= 2000)) (PreH92 : (1 <= all)) (PreH93 : (all <= 1000000000)) (PreH94 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH95 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH96 : (CopyMaxState original copied n_pre all )) (PreH97 : (LcmPrefixState copied n_pre all all )) (PreH98 : (Permutation copied sorted )) (PreH99 : (Permutation copied sorted )) (PreH100 : ((Zlength (sorted)) = n_pre)) (PreH101 : (all = mx_2)) (PreH102 : (i >= n_pre)) (PreH103 : (a_3 <> 0)) (PreH104 : (n_pre = (Zlength (original)))) (PreH105 : ((Zlength (copied)) = n_pre)) (PreH106 : (1 <= n_pre)) (PreH107 : (n_pre <= 2000)) (PreH108 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH109 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH110 : (1 <= mx_2)) (PreH111 : (mx_2 <= 1000000000)) (PreH112 : (0 <= i)) (PreH113 : (i <= n_pre)) (PreH114 : (1 <= all)) (PreH115 : (all <= (mx_2 + 1 ))) (PreH116 : (CopyMaxState original copied n_pre mx_2 )) (PreH117 : (LcmPrefixState copied i mx_2 all )) (PreH118 : (finished_i >= n_pre)) (PreH119 : (a_2 <> 0)) (PreH120 : (n_pre = (Zlength (original)))) (PreH121 : (1 <= n_pre)) (PreH122 : (n_pre <= 2000)) (PreH123 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH124 : (0 <= finished_i)) (PreH125 : (finished_i <= n_pre)) (PreH126 : (0 <= mx)) (PreH127 : (mx <= 1000000000)) (PreH128 : (CopyMaxState original copied finished_i mx )) (PreH129 : (retval <> 0)) (PreH130 : (original = a)) (PreH131 : (n_pre = (Zlength (original)))) (PreH132 : (1 <= n_pre)) (PreH133 : (n_pre <= 2000)) (PreH134 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorBestState a all_3 q_2 (z + 1 ) count )
.

Definition solver_entail_wit_12_2 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_3: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_2: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (l <> d)) (PreH2 : (present = 0)) (PreH3 : (i_2 >= n_pre)) (PreH4 : (a_5 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_4)) (PreH11 : (mx_4 <= 1000000000)) (PreH12 : (all_3 = mx_4)) (PreH13 : (1 <= q_2)) (PreH14 : (q_2 <= 31623)) (PreH15 : ((q_2 * q_2 ) <= mx_4)) (PreH16 : ((mx_4 % ( q_2 ) ) = 0)) (PreH17 : (0 <= z)) (PreH18 : (z < 2)) (PreH19 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_4)) (PreH22 : (0 <= ans_2)) (PreH23 : (ans_2 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_4 )) (PreH35 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z_2 < 2)) (PreH40 : (a_6 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_5)) (PreH47 : (mx_5 <= 1000000000)) (PreH48 : (all_4 = mx_5)) (PreH49 : (1 <= q_3)) (PreH50 : (q_3 <= 31623)) (PreH51 : ((q_3 * q_3 ) <= mx_5)) (PreH52 : ((mx_5 % ( q_3 ) ) = 0)) (PreH53 : (0 <= z_2)) (PreH54 : (z_2 <= 2)) (PreH55 : (0 <= ans_3)) (PreH56 : (ans_3 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_5 )) (PreH60 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
|--
  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= (z + 1 )) ” 
  &&  “ ((z + 1 ) <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 (z + 1 ) ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_3: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_2: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (l <> d)) (PreH2 : (present = 0)) (PreH3 : (i_2 >= n_pre)) (PreH4 : (a_5 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_4)) (PreH11 : (mx_4 <= 1000000000)) (PreH12 : (all_3 = mx_4)) (PreH13 : (1 <= q_2)) (PreH14 : (q_2 <= 31623)) (PreH15 : ((q_2 * q_2 ) <= mx_4)) (PreH16 : ((mx_4 % ( q_2 ) ) = 0)) (PreH17 : (0 <= z)) (PreH18 : (z < 2)) (PreH19 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_4)) (PreH22 : (0 <= ans_2)) (PreH23 : (ans_2 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_4 )) (PreH35 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z_2 < 2)) (PreH40 : (a_6 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_5)) (PreH47 : (mx_5 <= 1000000000)) (PreH48 : (all_4 = mx_5)) (PreH49 : (1 <= q_3)) (PreH50 : (q_3 <= 31623)) (PreH51 : ((q_3 * q_3 ) <= mx_5)) (PreH52 : ((mx_5 % ( q_3 ) ) = 0)) (PreH53 : (0 <= z_2)) (PreH54 : (z_2 <= 2)) (PreH55 : (0 <= ans_3)) (PreH56 : (ans_3 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_5 )) (PreH60 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorBestState a all_3 q_2 (z + 1 ) ans_2 ) ”
  &&  emp
).

Definition solver_entail_wit_12_2_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_3: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_2: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (l <> d)) (PreH2 : (present = 0)) (PreH3 : (i_2 >= n_pre)) (PreH4 : (a_5 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_4)) (PreH11 : (mx_4 <= 1000000000)) (PreH12 : (all_3 = mx_4)) (PreH13 : (1 <= q_2)) (PreH14 : (q_2 <= 31623)) (PreH15 : ((q_2 * q_2 ) <= mx_4)) (PreH16 : ((mx_4 % ( q_2 ) ) = 0)) (PreH17 : (0 <= z)) (PreH18 : (z < 2)) (PreH19 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_4)) (PreH22 : (0 <= ans_2)) (PreH23 : (ans_2 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_4 )) (PreH35 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z_2 < 2)) (PreH40 : (a_6 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_5)) (PreH47 : (mx_5 <= 1000000000)) (PreH48 : (all_4 = mx_5)) (PreH49 : (1 <= q_3)) (PreH50 : (q_3 <= 31623)) (PreH51 : ((q_3 * q_3 ) <= mx_5)) (PreH52 : ((mx_5 % ( q_3 ) ) = 0)) (PreH53 : (0 <= z_2)) (PreH54 : (z_2 <= 2)) (PreH55 : (0 <= ans_3)) (PreH56 : (ans_3 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_5 )) (PreH60 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorBestState a all_3 q_2 (z + 1 ) ans_2 )
.

Definition solver_entail_wit_12_3 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_3: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_2: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (present <> 0)) (PreH2 : (i_2 >= n_pre)) (PreH3 : (a_5 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_4)) (PreH10 : (mx_4 <= 1000000000)) (PreH11 : (all_3 = mx_4)) (PreH12 : (1 <= q_2)) (PreH13 : (q_2 <= 31623)) (PreH14 : ((q_2 * q_2 ) <= mx_4)) (PreH15 : ((mx_4 % ( q_2 ) ) = 0)) (PreH16 : (0 <= z)) (PreH17 : (z < 2)) (PreH18 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_4)) (PreH21 : (0 <= ans_2)) (PreH22 : (ans_2 <= n_pre)) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i_2)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_4 )) (PreH34 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH37 : (DivisorScanState sorted d i_2 present count l )) (PreH38 : (z_2 < 2)) (PreH39 : (a_6 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_5)) (PreH46 : (mx_5 <= 1000000000)) (PreH47 : (all_4 = mx_5)) (PreH48 : (1 <= q_3)) (PreH49 : (q_3 <= 31623)) (PreH50 : ((q_3 * q_3 ) <= mx_5)) (PreH51 : ((mx_5 % ( q_3 ) ) = 0)) (PreH52 : (0 <= z_2)) (PreH53 : (z_2 <= 2)) (PreH54 : (0 <= ans_3)) (PreH55 : (ans_3 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_5 )) (PreH59 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i)) (PreH111 : (i <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
|--
  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= (z + 1 )) ” 
  &&  “ ((z + 1 ) <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 (z + 1 ) ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_3: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_2: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (present <> 0)) (PreH2 : (i_2 >= n_pre)) (PreH3 : (a_5 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_4)) (PreH10 : (mx_4 <= 1000000000)) (PreH11 : (all_3 = mx_4)) (PreH12 : (1 <= q_2)) (PreH13 : (q_2 <= 31623)) (PreH14 : ((q_2 * q_2 ) <= mx_4)) (PreH15 : ((mx_4 % ( q_2 ) ) = 0)) (PreH16 : (0 <= z)) (PreH17 : (z < 2)) (PreH18 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_4)) (PreH21 : (0 <= ans_2)) (PreH22 : (ans_2 <= n_pre)) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i_2)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_4 )) (PreH34 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH37 : (DivisorScanState sorted d i_2 present count l )) (PreH38 : (z_2 < 2)) (PreH39 : (a_6 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_5)) (PreH46 : (mx_5 <= 1000000000)) (PreH47 : (all_4 = mx_5)) (PreH48 : (1 <= q_3)) (PreH49 : (q_3 <= 31623)) (PreH50 : ((q_3 * q_3 ) <= mx_5)) (PreH51 : ((mx_5 % ( q_3 ) ) = 0)) (PreH52 : (0 <= z_2)) (PreH53 : (z_2 <= 2)) (PreH54 : (0 <= ans_3)) (PreH55 : (ans_3 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_5 )) (PreH59 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i)) (PreH111 : (i <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorBestState a all_3 q_2 (z + 1 ) ans_2 ) ”
  &&  emp
).

Definition solver_entail_wit_12_3_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_3: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_2: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (present <> 0)) (PreH2 : (i_2 >= n_pre)) (PreH3 : (a_5 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_4)) (PreH10 : (mx_4 <= 1000000000)) (PreH11 : (all_3 = mx_4)) (PreH12 : (1 <= q_2)) (PreH13 : (q_2 <= 31623)) (PreH14 : ((q_2 * q_2 ) <= mx_4)) (PreH15 : ((mx_4 % ( q_2 ) ) = 0)) (PreH16 : (0 <= z)) (PreH17 : (z < 2)) (PreH18 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_4)) (PreH21 : (0 <= ans_2)) (PreH22 : (ans_2 <= n_pre)) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i_2)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_4 )) (PreH34 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH37 : (DivisorScanState sorted d i_2 present count l )) (PreH38 : (z_2 < 2)) (PreH39 : (a_6 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_5)) (PreH46 : (mx_5 <= 1000000000)) (PreH47 : (all_4 = mx_5)) (PreH48 : (1 <= q_3)) (PreH49 : (q_3 <= 31623)) (PreH50 : ((q_3 * q_3 ) <= mx_5)) (PreH51 : ((mx_5 % ( q_3 ) ) = 0)) (PreH52 : (0 <= z_2)) (PreH53 : (z_2 <= 2)) (PreH54 : (0 <= ans_3)) (PreH55 : (ans_3 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_5 )) (PreH59 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i)) (PreH111 : (i <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorBestState a all_3 q_2 (z + 1 ) ans_2 )
.

Definition solver_entail_wit_12_4 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_3: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_2: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (count <= ans_2)) (PreH2 : (l = d)) (PreH3 : (present = 0)) (PreH4 : (i_2 >= n_pre)) (PreH5 : (a_5 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (1 <= mx_4)) (PreH12 : (mx_4 <= 1000000000)) (PreH13 : (all_3 = mx_4)) (PreH14 : (1 <= q_2)) (PreH15 : (q_2 <= 31623)) (PreH16 : ((q_2 * q_2 ) <= mx_4)) (PreH17 : ((mx_4 % ( q_2 ) ) = 0)) (PreH18 : (0 <= z)) (PreH19 : (z < 2)) (PreH20 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH21 : (1 <= d)) (PreH22 : (d <= mx_4)) (PreH23 : (0 <= ans_2)) (PreH24 : (ans_2 <= n_pre)) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 <= n_pre)) (PreH27 : (0 <= present)) (PreH28 : (present <= 1)) (PreH29 : (0 <= count)) (PreH30 : (count <= i_2)) (PreH31 : (1 <= l)) (PreH32 : (l <= (d + 1 ))) (PreH33 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH34 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH35 : (CopyMaxState original copied n_pre mx_4 )) (PreH36 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH37 : (Permutation copied sorted )) (PreH38 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH39 : (DivisorScanState sorted d i_2 present count l )) (PreH40 : (z_2 < 2)) (PreH41 : (a_6 <> 0)) (PreH42 : (n_pre = (Zlength (original)))) (PreH43 : ((Zlength (copied)) = n_pre)) (PreH44 : ((Zlength (sorted)) = n_pre)) (PreH45 : (1 <= n_pre)) (PreH46 : (n_pre <= 2000)) (PreH47 : (1 <= mx_5)) (PreH48 : (mx_5 <= 1000000000)) (PreH49 : (all_4 = mx_5)) (PreH50 : (1 <= q_3)) (PreH51 : (q_3 <= 31623)) (PreH52 : ((q_3 * q_3 ) <= mx_5)) (PreH53 : ((mx_5 % ( q_3 ) ) = 0)) (PreH54 : (0 <= z_2)) (PreH55 : (z_2 <= 2)) (PreH56 : (0 <= ans_3)) (PreH57 : (ans_3 <= n_pre)) (PreH58 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH59 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH60 : (CopyMaxState original copied n_pre mx_5 )) (PreH61 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH62 : (Permutation copied sorted )) (PreH63 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH64 : ((mx_3 % ( q ) ) = 0)) (PreH65 : ((q * q ) <= mx_3)) (PreH66 : (a_4 <> 0)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : ((Zlength (copied)) = n_pre)) (PreH69 : ((Zlength (sorted)) = n_pre)) (PreH70 : (1 <= n_pre)) (PreH71 : (n_pre <= 2000)) (PreH72 : (1 <= mx_3)) (PreH73 : (mx_3 <= 1000000000)) (PreH74 : (all_2 = mx_3)) (PreH75 : (1 <= q)) (PreH76 : (q <= 31624)) (PreH77 : (0 <= ans)) (PreH78 : (ans <= n_pre)) (PreH79 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH80 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH81 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH82 : (CopyMaxState original copied n_pre mx_3 )) (PreH83 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH84 : (Permutation copied sorted )) (PreH85 : (DivisorBestState original mx_3 q 0 ans )) (PreH86 : (a_3 <> 0)) (PreH87 : (n_pre = (Zlength (original)))) (PreH88 : ((Zlength (copied)) = n_pre)) (PreH89 : ((Zlength (sorted)) = n_pre)) (PreH90 : (1 <= n_pre)) (PreH91 : (n_pre <= 2000)) (PreH92 : (1 <= all)) (PreH93 : (all <= 1000000000)) (PreH94 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH95 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH96 : (CopyMaxState original copied n_pre all )) (PreH97 : (LcmPrefixState copied n_pre all all )) (PreH98 : (Permutation copied sorted )) (PreH99 : (Permutation copied sorted )) (PreH100 : ((Zlength (sorted)) = n_pre)) (PreH101 : (all = mx_2)) (PreH102 : (i >= n_pre)) (PreH103 : (a_3 <> 0)) (PreH104 : (n_pre = (Zlength (original)))) (PreH105 : ((Zlength (copied)) = n_pre)) (PreH106 : (1 <= n_pre)) (PreH107 : (n_pre <= 2000)) (PreH108 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH109 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH110 : (1 <= mx_2)) (PreH111 : (mx_2 <= 1000000000)) (PreH112 : (0 <= i)) (PreH113 : (i <= n_pre)) (PreH114 : (1 <= all)) (PreH115 : (all <= (mx_2 + 1 ))) (PreH116 : (CopyMaxState original copied n_pre mx_2 )) (PreH117 : (LcmPrefixState copied i mx_2 all )) (PreH118 : (finished_i >= n_pre)) (PreH119 : (a_2 <> 0)) (PreH120 : (n_pre = (Zlength (original)))) (PreH121 : (1 <= n_pre)) (PreH122 : (n_pre <= 2000)) (PreH123 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH124 : (0 <= finished_i)) (PreH125 : (finished_i <= n_pre)) (PreH126 : (0 <= mx)) (PreH127 : (mx <= 1000000000)) (PreH128 : (CopyMaxState original copied finished_i mx )) (PreH129 : (retval <> 0)) (PreH130 : (original = a)) (PreH131 : (n_pre = (Zlength (original)))) (PreH132 : (1 <= n_pre)) (PreH133 : (n_pre <= 2000)) (PreH134 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
|--
  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= (z + 1 )) ” 
  &&  “ ((z + 1 ) <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 (z + 1 ) ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_3: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_2: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (count <= ans_2)) (PreH2 : (l = d)) (PreH3 : (present = 0)) (PreH4 : (i_2 >= n_pre)) (PreH5 : (a_5 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (1 <= mx_4)) (PreH12 : (mx_4 <= 1000000000)) (PreH13 : (all_3 = mx_4)) (PreH14 : (1 <= q_2)) (PreH15 : (q_2 <= 31623)) (PreH16 : ((q_2 * q_2 ) <= mx_4)) (PreH17 : ((mx_4 % ( q_2 ) ) = 0)) (PreH18 : (0 <= z)) (PreH19 : (z < 2)) (PreH20 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH21 : (1 <= d)) (PreH22 : (d <= mx_4)) (PreH23 : (0 <= ans_2)) (PreH24 : (ans_2 <= n_pre)) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 <= n_pre)) (PreH27 : (0 <= present)) (PreH28 : (present <= 1)) (PreH29 : (0 <= count)) (PreH30 : (count <= i_2)) (PreH31 : (1 <= l)) (PreH32 : (l <= (d + 1 ))) (PreH33 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH34 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH35 : (CopyMaxState original copied n_pre mx_4 )) (PreH36 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH37 : (Permutation copied sorted )) (PreH38 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH39 : (DivisorScanState sorted d i_2 present count l )) (PreH40 : (z_2 < 2)) (PreH41 : (a_6 <> 0)) (PreH42 : (n_pre = (Zlength (original)))) (PreH43 : ((Zlength (copied)) = n_pre)) (PreH44 : ((Zlength (sorted)) = n_pre)) (PreH45 : (1 <= n_pre)) (PreH46 : (n_pre <= 2000)) (PreH47 : (1 <= mx_5)) (PreH48 : (mx_5 <= 1000000000)) (PreH49 : (all_4 = mx_5)) (PreH50 : (1 <= q_3)) (PreH51 : (q_3 <= 31623)) (PreH52 : ((q_3 * q_3 ) <= mx_5)) (PreH53 : ((mx_5 % ( q_3 ) ) = 0)) (PreH54 : (0 <= z_2)) (PreH55 : (z_2 <= 2)) (PreH56 : (0 <= ans_3)) (PreH57 : (ans_3 <= n_pre)) (PreH58 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH59 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH60 : (CopyMaxState original copied n_pre mx_5 )) (PreH61 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH62 : (Permutation copied sorted )) (PreH63 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH64 : ((mx_3 % ( q ) ) = 0)) (PreH65 : ((q * q ) <= mx_3)) (PreH66 : (a_4 <> 0)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : ((Zlength (copied)) = n_pre)) (PreH69 : ((Zlength (sorted)) = n_pre)) (PreH70 : (1 <= n_pre)) (PreH71 : (n_pre <= 2000)) (PreH72 : (1 <= mx_3)) (PreH73 : (mx_3 <= 1000000000)) (PreH74 : (all_2 = mx_3)) (PreH75 : (1 <= q)) (PreH76 : (q <= 31624)) (PreH77 : (0 <= ans)) (PreH78 : (ans <= n_pre)) (PreH79 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH80 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH81 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH82 : (CopyMaxState original copied n_pre mx_3 )) (PreH83 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH84 : (Permutation copied sorted )) (PreH85 : (DivisorBestState original mx_3 q 0 ans )) (PreH86 : (a_3 <> 0)) (PreH87 : (n_pre = (Zlength (original)))) (PreH88 : ((Zlength (copied)) = n_pre)) (PreH89 : ((Zlength (sorted)) = n_pre)) (PreH90 : (1 <= n_pre)) (PreH91 : (n_pre <= 2000)) (PreH92 : (1 <= all)) (PreH93 : (all <= 1000000000)) (PreH94 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH95 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH96 : (CopyMaxState original copied n_pre all )) (PreH97 : (LcmPrefixState copied n_pre all all )) (PreH98 : (Permutation copied sorted )) (PreH99 : (Permutation copied sorted )) (PreH100 : ((Zlength (sorted)) = n_pre)) (PreH101 : (all = mx_2)) (PreH102 : (i >= n_pre)) (PreH103 : (a_3 <> 0)) (PreH104 : (n_pre = (Zlength (original)))) (PreH105 : ((Zlength (copied)) = n_pre)) (PreH106 : (1 <= n_pre)) (PreH107 : (n_pre <= 2000)) (PreH108 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH109 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH110 : (1 <= mx_2)) (PreH111 : (mx_2 <= 1000000000)) (PreH112 : (0 <= i)) (PreH113 : (i <= n_pre)) (PreH114 : (1 <= all)) (PreH115 : (all <= (mx_2 + 1 ))) (PreH116 : (CopyMaxState original copied n_pre mx_2 )) (PreH117 : (LcmPrefixState copied i mx_2 all )) (PreH118 : (finished_i >= n_pre)) (PreH119 : (a_2 <> 0)) (PreH120 : (n_pre = (Zlength (original)))) (PreH121 : (1 <= n_pre)) (PreH122 : (n_pre <= 2000)) (PreH123 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH124 : (0 <= finished_i)) (PreH125 : (finished_i <= n_pre)) (PreH126 : (0 <= mx)) (PreH127 : (mx <= 1000000000)) (PreH128 : (CopyMaxState original copied finished_i mx )) (PreH129 : (retval <> 0)) (PreH130 : (original = a)) (PreH131 : (n_pre = (Zlength (original)))) (PreH132 : (1 <= n_pre)) (PreH133 : (n_pre <= 2000)) (PreH134 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorBestState a all_3 q_2 (z + 1 ) ans_2 ) ”
  &&  emp
).

Definition solver_entail_wit_12_4_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_3: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_2: Z) (d: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (count <= ans_2)) (PreH2 : (l = d)) (PreH3 : (present = 0)) (PreH4 : (i_2 >= n_pre)) (PreH5 : (a_5 <> 0)) (PreH6 : (n_pre = (Zlength (original)))) (PreH7 : ((Zlength (copied)) = n_pre)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (1 <= mx_4)) (PreH12 : (mx_4 <= 1000000000)) (PreH13 : (all_3 = mx_4)) (PreH14 : (1 <= q_2)) (PreH15 : (q_2 <= 31623)) (PreH16 : ((q_2 * q_2 ) <= mx_4)) (PreH17 : ((mx_4 % ( q_2 ) ) = 0)) (PreH18 : (0 <= z)) (PreH19 : (z < 2)) (PreH20 : (d = (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))) (PreH21 : (1 <= d)) (PreH22 : (d <= mx_4)) (PreH23 : (0 <= ans_2)) (PreH24 : (ans_2 <= n_pre)) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 <= n_pre)) (PreH27 : (0 <= present)) (PreH28 : (present <= 1)) (PreH29 : (0 <= count)) (PreH30 : (count <= i_2)) (PreH31 : (1 <= l)) (PreH32 : (l <= (d + 1 ))) (PreH33 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH34 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH35 : (CopyMaxState original copied n_pre mx_4 )) (PreH36 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH37 : (Permutation copied sorted )) (PreH38 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH39 : (DivisorScanState sorted d i_2 present count l )) (PreH40 : (z_2 < 2)) (PreH41 : (a_6 <> 0)) (PreH42 : (n_pre = (Zlength (original)))) (PreH43 : ((Zlength (copied)) = n_pre)) (PreH44 : ((Zlength (sorted)) = n_pre)) (PreH45 : (1 <= n_pre)) (PreH46 : (n_pre <= 2000)) (PreH47 : (1 <= mx_5)) (PreH48 : (mx_5 <= 1000000000)) (PreH49 : (all_4 = mx_5)) (PreH50 : (1 <= q_3)) (PreH51 : (q_3 <= 31623)) (PreH52 : ((q_3 * q_3 ) <= mx_5)) (PreH53 : ((mx_5 % ( q_3 ) ) = 0)) (PreH54 : (0 <= z_2)) (PreH55 : (z_2 <= 2)) (PreH56 : (0 <= ans_3)) (PreH57 : (ans_3 <= n_pre)) (PreH58 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH59 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH60 : (CopyMaxState original copied n_pre mx_5 )) (PreH61 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH62 : (Permutation copied sorted )) (PreH63 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH64 : ((mx_3 % ( q ) ) = 0)) (PreH65 : ((q * q ) <= mx_3)) (PreH66 : (a_4 <> 0)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : ((Zlength (copied)) = n_pre)) (PreH69 : ((Zlength (sorted)) = n_pre)) (PreH70 : (1 <= n_pre)) (PreH71 : (n_pre <= 2000)) (PreH72 : (1 <= mx_3)) (PreH73 : (mx_3 <= 1000000000)) (PreH74 : (all_2 = mx_3)) (PreH75 : (1 <= q)) (PreH76 : (q <= 31624)) (PreH77 : (0 <= ans)) (PreH78 : (ans <= n_pre)) (PreH79 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH80 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH81 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH82 : (CopyMaxState original copied n_pre mx_3 )) (PreH83 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH84 : (Permutation copied sorted )) (PreH85 : (DivisorBestState original mx_3 q 0 ans )) (PreH86 : (a_3 <> 0)) (PreH87 : (n_pre = (Zlength (original)))) (PreH88 : ((Zlength (copied)) = n_pre)) (PreH89 : ((Zlength (sorted)) = n_pre)) (PreH90 : (1 <= n_pre)) (PreH91 : (n_pre <= 2000)) (PreH92 : (1 <= all)) (PreH93 : (all <= 1000000000)) (PreH94 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH95 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH96 : (CopyMaxState original copied n_pre all )) (PreH97 : (LcmPrefixState copied n_pre all all )) (PreH98 : (Permutation copied sorted )) (PreH99 : (Permutation copied sorted )) (PreH100 : ((Zlength (sorted)) = n_pre)) (PreH101 : (all = mx_2)) (PreH102 : (i >= n_pre)) (PreH103 : (a_3 <> 0)) (PreH104 : (n_pre = (Zlength (original)))) (PreH105 : ((Zlength (copied)) = n_pre)) (PreH106 : (1 <= n_pre)) (PreH107 : (n_pre <= 2000)) (PreH108 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH109 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH110 : (1 <= mx_2)) (PreH111 : (mx_2 <= 1000000000)) (PreH112 : (0 <= i)) (PreH113 : (i <= n_pre)) (PreH114 : (1 <= all)) (PreH115 : (all <= (mx_2 + 1 ))) (PreH116 : (CopyMaxState original copied n_pre mx_2 )) (PreH117 : (LcmPrefixState copied i mx_2 all )) (PreH118 : (finished_i >= n_pre)) (PreH119 : (a_2 <> 0)) (PreH120 : (n_pre = (Zlength (original)))) (PreH121 : (1 <= n_pre)) (PreH122 : (n_pre <= 2000)) (PreH123 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH124 : (0 <= finished_i)) (PreH125 : (finished_i <= n_pre)) (PreH126 : (0 <= mx)) (PreH127 : (mx <= 1000000000)) (PreH128 : (CopyMaxState original copied finished_i mx )) (PreH129 : (retval <> 0)) (PreH130 : (original = a)) (PreH131 : (n_pre = (Zlength (original)))) (PreH132 : (1 <= n_pre)) (PreH133 : (n_pre <= 2000)) (PreH134 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorBestState a all_3 q_2 (z + 1 ) ans_2 )
.

Definition solver_entail_wit_13 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((q * q ) > mx_3)) (PreH2 : (a_4 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_3)) (PreH9 : (mx_3 <= 1000000000)) (PreH10 : (all_2 = mx_3)) (PreH11 : (1 <= q)) (PreH12 : (q <= 31624)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= n_pre)) (PreH15 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH16 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH18 : (CopyMaxState original copied n_pre mx_3 )) (PreH19 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH20 : (Permutation copied sorted )) (PreH21 : (DivisorBestState original mx_3 q 0 ans )) (PreH22 : (a_3 <> 0)) (PreH23 : (n_pre = (Zlength (original)))) (PreH24 : ((Zlength (copied)) = n_pre)) (PreH25 : ((Zlength (sorted)) = n_pre)) (PreH26 : (1 <= n_pre)) (PreH27 : (n_pre <= 2000)) (PreH28 : (1 <= all)) (PreH29 : (all <= 1000000000)) (PreH30 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH31 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH32 : (CopyMaxState original copied n_pre all )) (PreH33 : (LcmPrefixState copied n_pre all all )) (PreH34 : (Permutation copied sorted )) (PreH35 : (Permutation copied sorted )) (PreH36 : ((Zlength (sorted)) = n_pre)) (PreH37 : (all = mx_2)) (PreH38 : (i >= n_pre)) (PreH39 : (a_3 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : (1 <= n_pre)) (PreH43 : (n_pre <= 2000)) (PreH44 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH45 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH46 : (1 <= mx_2)) (PreH47 : (mx_2 <= 1000000000)) (PreH48 : (0 <= i)) (PreH49 : (i <= n_pre)) (PreH50 : (1 <= all)) (PreH51 : (all <= (mx_2 + 1 ))) (PreH52 : (CopyMaxState original copied n_pre mx_2 )) (PreH53 : (LcmPrefixState copied i mx_2 all )) (PreH54 : (finished_i >= n_pre)) (PreH55 : (a_2 <> 0)) (PreH56 : (n_pre = (Zlength (original)))) (PreH57 : (1 <= n_pre)) (PreH58 : (n_pre <= 2000)) (PreH59 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH60 : (0 <= finished_i)) (PreH61 : (finished_i <= n_pre)) (PreH62 : (0 <= mx)) (PreH63 : (mx <= 1000000000)) (PreH64 : (CopyMaxState original copied finished_i mx )) (PreH65 : (retval <> 0)) (PreH66 : (original = a)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (mx_3 = mx_3) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (Spec original ans ) ” 
  &&  “ ((q * q ) > mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (mx_3 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 mx_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((q * q ) > mx_3)) (PreH2 : (a_4 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_3)) (PreH9 : (mx_3 <= 1000000000)) (PreH10 : (all_2 = mx_3)) (PreH11 : (1 <= q)) (PreH12 : (q <= 31624)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= n_pre)) (PreH15 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH16 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH18 : (CopyMaxState original copied n_pre mx_3 )) (PreH19 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH20 : (Permutation copied sorted )) (PreH21 : (DivisorBestState original mx_3 q 0 ans )) (PreH22 : (a_3 <> 0)) (PreH23 : (n_pre = (Zlength (original)))) (PreH24 : ((Zlength (copied)) = n_pre)) (PreH25 : ((Zlength (sorted)) = n_pre)) (PreH26 : (1 <= n_pre)) (PreH27 : (n_pre <= 2000)) (PreH28 : (1 <= all)) (PreH29 : (all <= 1000000000)) (PreH30 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH31 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH32 : (CopyMaxState original copied n_pre all )) (PreH33 : (LcmPrefixState copied n_pre all all )) (PreH34 : (Permutation copied sorted )) (PreH35 : (Permutation copied sorted )) (PreH36 : ((Zlength (sorted)) = n_pre)) (PreH37 : (all = mx_2)) (PreH38 : (i >= n_pre)) (PreH39 : (a_3 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : (1 <= n_pre)) (PreH43 : (n_pre <= 2000)) (PreH44 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH45 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH46 : (1 <= mx_2)) (PreH47 : (mx_2 <= 1000000000)) (PreH48 : (0 <= i)) (PreH49 : (i <= n_pre)) (PreH50 : (1 <= all)) (PreH51 : (all <= (mx_2 + 1 ))) (PreH52 : (CopyMaxState original copied n_pre mx_2 )) (PreH53 : (LcmPrefixState copied i mx_2 all )) (PreH54 : (finished_i >= n_pre)) (PreH55 : (a_2 <> 0)) (PreH56 : (n_pre = (Zlength (original)))) (PreH57 : (1 <= n_pre)) (PreH58 : (n_pre <= 2000)) (PreH59 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH60 : (0 <= finished_i)) (PreH61 : (finished_i <= n_pre)) (PreH62 : (0 <= mx)) (PreH63 : (mx <= 1000000000)) (PreH64 : (CopyMaxState original copied finished_i mx )) (PreH65 : (retval <> 0)) (PreH66 : (original = a)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (Spec a ans ) ”
  &&  emp
).

Definition solver_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((q * q ) > mx_3)) (PreH2 : (a_4 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_3)) (PreH9 : (mx_3 <= 1000000000)) (PreH10 : (all_2 = mx_3)) (PreH11 : (1 <= q)) (PreH12 : (q <= 31624)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= n_pre)) (PreH15 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH16 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH18 : (CopyMaxState original copied n_pre mx_3 )) (PreH19 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH20 : (Permutation copied sorted )) (PreH21 : (DivisorBestState original mx_3 q 0 ans )) (PreH22 : (a_3 <> 0)) (PreH23 : (n_pre = (Zlength (original)))) (PreH24 : ((Zlength (copied)) = n_pre)) (PreH25 : ((Zlength (sorted)) = n_pre)) (PreH26 : (1 <= n_pre)) (PreH27 : (n_pre <= 2000)) (PreH28 : (1 <= all)) (PreH29 : (all <= 1000000000)) (PreH30 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH31 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH32 : (CopyMaxState original copied n_pre all )) (PreH33 : (LcmPrefixState copied n_pre all all )) (PreH34 : (Permutation copied sorted )) (PreH35 : (Permutation copied sorted )) (PreH36 : ((Zlength (sorted)) = n_pre)) (PreH37 : (all = mx_2)) (PreH38 : (i >= n_pre)) (PreH39 : (a_3 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : (1 <= n_pre)) (PreH43 : (n_pre <= 2000)) (PreH44 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH45 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH46 : (1 <= mx_2)) (PreH47 : (mx_2 <= 1000000000)) (PreH48 : (0 <= i)) (PreH49 : (i <= n_pre)) (PreH50 : (1 <= all)) (PreH51 : (all <= (mx_2 + 1 ))) (PreH52 : (CopyMaxState original copied n_pre mx_2 )) (PreH53 : (LcmPrefixState copied i mx_2 all )) (PreH54 : (finished_i >= n_pre)) (PreH55 : (a_2 <> 0)) (PreH56 : (n_pre = (Zlength (original)))) (PreH57 : (1 <= n_pre)) (PreH58 : (n_pre <= 2000)) (PreH59 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH60 : (0 <= finished_i)) (PreH61 : (finished_i <= n_pre)) (PreH62 : (0 <= mx)) (PreH63 : (mx <= 1000000000)) (PreH64 : (CopyMaxState original copied finished_i mx )) (PreH65 : (retval <> 0)) (PreH66 : (original = a)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (Spec a ans )
.

Definition solver_entail_wit_14_1 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans_2: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (ans: Z) (z: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : (z >= 2)) (PreH2 : (a_4 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_3)) (PreH9 : (mx_3 <= 1000000000)) (PreH10 : (all_2 = mx_3)) (PreH11 : (1 <= q)) (PreH12 : (q <= 31623)) (PreH13 : ((q * q ) <= mx_3)) (PreH14 : ((mx_3 % ( q ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_3 )) (PreH22 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_3 q z ans )) (PreH25 : ((mx_4 % ( q_2 ) ) = 0)) (PreH26 : ((q_2 * q_2 ) <= mx_4)) (PreH27 : (a_5 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_4)) (PreH34 : (mx_4 <= 1000000000)) (PreH35 : (all_3 = mx_4)) (PreH36 : (1 <= q_2)) (PreH37 : (q_2 <= 31624)) (PreH38 : (0 <= ans_2)) (PreH39 : (ans_2 <= n_pre)) (PreH40 : (((q_2 - 1 ) * (q_2 - 1 ) ) <= mx_4)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_4 )) (PreH44 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_4 q_2 0 ans_2 )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= (q + 1 )) ” 
  &&  “ ((q + 1 ) <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ ((((q + 1 ) - 1 ) * ((q + 1 ) - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 (q + 1 ) 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans_2: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (ans: Z) (z: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : (z >= 2)) (PreH2 : (a_4 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_3)) (PreH9 : (mx_3 <= 1000000000)) (PreH10 : (all_2 = mx_3)) (PreH11 : (1 <= q)) (PreH12 : (q <= 31623)) (PreH13 : ((q * q ) <= mx_3)) (PreH14 : ((mx_3 % ( q ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_3 )) (PreH22 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_3 q z ans )) (PreH25 : ((mx_4 % ( q_2 ) ) = 0)) (PreH26 : ((q_2 * q_2 ) <= mx_4)) (PreH27 : (a_5 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_4)) (PreH34 : (mx_4 <= 1000000000)) (PreH35 : (all_3 = mx_4)) (PreH36 : (1 <= q_2)) (PreH37 : (q_2 <= 31624)) (PreH38 : (0 <= ans_2)) (PreH39 : (ans_2 <= n_pre)) (PreH40 : (((q_2 - 1 ) * (q_2 - 1 ) ) <= mx_4)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_4 )) (PreH44 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_4 q_2 0 ans_2 )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorBestState a all_2 (q + 1 ) 0 ans ) ” 
  &&  “ ((((q + 1 ) - 1 ) * ((q + 1 ) - 1 ) ) <= all_2) ”
  &&  emp
).

Definition solver_entail_wit_14_1_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans_2: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (ans: Z) (z: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : (z >= 2)) (PreH2 : (a_4 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_3)) (PreH9 : (mx_3 <= 1000000000)) (PreH10 : (all_2 = mx_3)) (PreH11 : (1 <= q)) (PreH12 : (q <= 31623)) (PreH13 : ((q * q ) <= mx_3)) (PreH14 : ((mx_3 % ( q ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_3 )) (PreH22 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_3 q z ans )) (PreH25 : ((mx_4 % ( q_2 ) ) = 0)) (PreH26 : ((q_2 * q_2 ) <= mx_4)) (PreH27 : (a_5 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_4)) (PreH34 : (mx_4 <= 1000000000)) (PreH35 : (all_3 = mx_4)) (PreH36 : (1 <= q_2)) (PreH37 : (q_2 <= 31624)) (PreH38 : (0 <= ans_2)) (PreH39 : (ans_2 <= n_pre)) (PreH40 : (((q_2 - 1 ) * (q_2 - 1 ) ) <= mx_4)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_4 )) (PreH44 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_4 q_2 0 ans_2 )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorBestState a all_2 (q + 1 ) 0 ans )
.

Definition solver_entail_wit_14_1_split_goal_2 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans_2: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (ans: Z) (z: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : (z >= 2)) (PreH2 : (a_4 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_3)) (PreH9 : (mx_3 <= 1000000000)) (PreH10 : (all_2 = mx_3)) (PreH11 : (1 <= q)) (PreH12 : (q <= 31623)) (PreH13 : ((q * q ) <= mx_3)) (PreH14 : ((mx_3 % ( q ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_3 )) (PreH22 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_3 q z ans )) (PreH25 : ((mx_4 % ( q_2 ) ) = 0)) (PreH26 : ((q_2 * q_2 ) <= mx_4)) (PreH27 : (a_5 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_4)) (PreH34 : (mx_4 <= 1000000000)) (PreH35 : (all_3 = mx_4)) (PreH36 : (1 <= q_2)) (PreH37 : (q_2 <= 31624)) (PreH38 : (0 <= ans_2)) (PreH39 : (ans_2 <= n_pre)) (PreH40 : (((q_2 - 1 ) * (q_2 - 1 ) ) <= mx_4)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_4 )) (PreH44 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_4 q_2 0 ans_2 )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((((q + 1 ) - 1 ) * ((q + 1 ) - 1 ) ) <= all_2)
.

Definition solver_entail_wit_14_2 := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((mx_3 % ( q ) ) <> 0)) (PreH2 : ((q * q ) <= mx_3)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_3)) (PreH10 : (mx_3 <= 1000000000)) (PreH11 : (all_2 = mx_3)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx_3 )) (PreH20 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx_3 q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_2)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_2)) (PreH48 : (mx_2 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_2 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_2 )) (PreH54 : (LcmPrefixState copied i mx_2 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx)) (PreH64 : (mx <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= (q + 1 )) ” 
  &&  “ ((q + 1 ) <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ ((((q + 1 ) - 1 ) * ((q + 1 ) - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 (q + 1 ) 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
) \/
(
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((mx_3 % ( q ) ) <> 0)) (PreH2 : ((q * q ) <= mx_3)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_3)) (PreH10 : (mx_3 <= 1000000000)) (PreH11 : (all_2 = mx_3)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx_3 )) (PreH20 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx_3 q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_2)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_2)) (PreH48 : (mx_2 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_2 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_2 )) (PreH54 : (LcmPrefixState copied i mx_2 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx)) (PreH64 : (mx <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (DivisorBestState a all_2 (q + 1 ) 0 ans ) ” 
  &&  “ ((((q + 1 ) - 1 ) * ((q + 1 ) - 1 ) ) <= all_2) ”
  &&  emp
).

Definition solver_entail_wit_14_2_split_goal_1 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((mx_3 % ( q ) ) <> 0)) (PreH2 : ((q * q ) <= mx_3)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_3)) (PreH10 : (mx_3 <= 1000000000)) (PreH11 : (all_2 = mx_3)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx_3 )) (PreH20 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx_3 q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_2)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_2)) (PreH48 : (mx_2 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_2 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_2 )) (PreH54 : (LcmPrefixState copied i mx_2 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx)) (PreH64 : (mx <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (DivisorBestState a all_2 (q + 1 ) 0 ans )
.

Definition solver_entail_wit_14_2_split_goal_2 := 
forall (n_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : ((mx_3 % ( q ) ) <> 0)) (PreH2 : ((q * q ) <= mx_3)) (PreH3 : (a_4 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_3)) (PreH10 : (mx_3 <= 1000000000)) (PreH11 : (all_2 = mx_3)) (PreH12 : (1 <= q)) (PreH13 : (q <= 31624)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= n_pre)) (PreH16 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH19 : (CopyMaxState original copied n_pre mx_3 )) (PreH20 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH21 : (Permutation copied sorted )) (PreH22 : (DivisorBestState original mx_3 q 0 ans )) (PreH23 : (a_3 <> 0)) (PreH24 : (n_pre = (Zlength (original)))) (PreH25 : ((Zlength (copied)) = n_pre)) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : (1 <= n_pre)) (PreH28 : (n_pre <= 2000)) (PreH29 : (1 <= all)) (PreH30 : (all <= 1000000000)) (PreH31 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH32 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre all )) (PreH34 : (LcmPrefixState copied n_pre all all )) (PreH35 : (Permutation copied sorted )) (PreH36 : (Permutation copied sorted )) (PreH37 : ((Zlength (sorted)) = n_pre)) (PreH38 : (all = mx_2)) (PreH39 : (i >= n_pre)) (PreH40 : (a_3 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH46 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH47 : (1 <= mx_2)) (PreH48 : (mx_2 <= 1000000000)) (PreH49 : (0 <= i)) (PreH50 : (i <= n_pre)) (PreH51 : (1 <= all)) (PreH52 : (all <= (mx_2 + 1 ))) (PreH53 : (CopyMaxState original copied n_pre mx_2 )) (PreH54 : (LcmPrefixState copied i mx_2 all )) (PreH55 : (finished_i >= n_pre)) (PreH56 : (a_2 <> 0)) (PreH57 : (n_pre = (Zlength (original)))) (PreH58 : (1 <= n_pre)) (PreH59 : (n_pre <= 2000)) (PreH60 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH61 : (0 <= finished_i)) (PreH62 : (finished_i <= n_pre)) (PreH63 : (0 <= mx)) (PreH64 : (mx <= 1000000000)) (PreH65 : (CopyMaxState original copied finished_i mx )) (PreH66 : (retval <> 0)) (PreH67 : (original = a)) (PreH68 : (n_pre = (Zlength (original)))) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((((q + 1 ) - 1 ) * ((q + 1 ) - 1 ) ) <= all_2)
.

Definition solver_return_wit_1 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : (a_4 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= all_2)) (PreH7 : (all_2 <= 1000000000)) (PreH8 : (0 <= ans)) (PreH9 : (ans <= n_pre)) (PreH10 : (Spec original ans )) (PreH11 : ((q * q ) > mx_3)) (PreH12 : (a_4 <> 0)) (PreH13 : (n_pre = (Zlength (original)))) (PreH14 : ((Zlength (copied)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (1 <= mx_3)) (PreH19 : (mx_3 <= 1000000000)) (PreH20 : (all_2 = mx_3)) (PreH21 : (1 <= q)) (PreH22 : (q <= 31624)) (PreH23 : (0 <= ans)) (PreH24 : (ans <= n_pre)) (PreH25 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH26 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH27 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH28 : (CopyMaxState original copied n_pre mx_3 )) (PreH29 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH30 : (Permutation copied sorted )) (PreH31 : (DivisorBestState original mx_3 q 0 ans )) (PreH32 : (a_3 <> 0)) (PreH33 : (n_pre = (Zlength (original)))) (PreH34 : ((Zlength (copied)) = n_pre)) (PreH35 : ((Zlength (sorted)) = n_pre)) (PreH36 : (1 <= n_pre)) (PreH37 : (n_pre <= 2000)) (PreH38 : (1 <= all)) (PreH39 : (all <= 1000000000)) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH42 : (CopyMaxState original copied n_pre all )) (PreH43 : (LcmPrefixState copied n_pre all all )) (PreH44 : (Permutation copied sorted )) (PreH45 : (Permutation copied sorted )) (PreH46 : ((Zlength (sorted)) = n_pre)) (PreH47 : (all = mx_2)) (PreH48 : (i >= n_pre)) (PreH49 : (a_3 <> 0)) (PreH50 : (n_pre = (Zlength (original)))) (PreH51 : ((Zlength (copied)) = n_pre)) (PreH52 : (1 <= n_pre)) (PreH53 : (n_pre <= 2000)) (PreH54 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH55 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH56 : (1 <= mx_2)) (PreH57 : (mx_2 <= 1000000000)) (PreH58 : (0 <= i)) (PreH59 : (i <= n_pre)) (PreH60 : (1 <= all)) (PreH61 : (all <= (mx_2 + 1 ))) (PreH62 : (CopyMaxState original copied n_pre mx_2 )) (PreH63 : (LcmPrefixState copied i mx_2 all )) (PreH64 : (finished_i >= n_pre)) (PreH65 : (a_2 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH70 : (0 <= finished_i)) (PreH71 : (finished_i <= n_pre)) (PreH72 : (0 <= mx)) (PreH73 : (mx <= 1000000000)) (PreH74 : (CopyMaxState original copied finished_i mx )) (PreH75 : (retval <> 0)) (PreH76 : (original = a)) (PreH77 : (n_pre = (Zlength (original)))) (PreH78 : (1 <= n_pre)) (PreH79 : (n_pre <= 2000)) (PreH80 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
|--
  “ (Spec a ans ) ”
  &&  (IntArray.full input_pre n_pre a )
.

Definition solver_return_wit_2 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (PreH1 : (a_3 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= mx_2)) (PreH7 : (mx_2 <= 1000000000)) (PreH8 : (all <> mx_2)) (PreH9 : (CopyMaxState original copied n_pre mx_2 )) (PreH10 : (LcmPrefixState copied n_pre mx_2 all )) (PreH11 : (Spec original n_pre )) (PreH12 : (all <> mx_2)) (PreH13 : (i >= n_pre)) (PreH14 : (a_3 <> 0)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : ((Zlength (copied)) = n_pre)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH20 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH21 : (1 <= mx_2)) (PreH22 : (mx_2 <= 1000000000)) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (1 <= all)) (PreH26 : (all <= (mx_2 + 1 ))) (PreH27 : (CopyMaxState original copied n_pre mx_2 )) (PreH28 : (LcmPrefixState copied i mx_2 all )) (PreH29 : (finished_i >= n_pre)) (PreH30 : (a_2 <> 0)) (PreH31 : (n_pre = (Zlength (original)))) (PreH32 : (1 <= n_pre)) (PreH33 : (n_pre <= 2000)) (PreH34 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH35 : (0 <= finished_i)) (PreH36 : (finished_i <= n_pre)) (PreH37 : (0 <= mx)) (PreH38 : (mx <= 1000000000)) (PreH39 : (CopyMaxState original copied finished_i mx )) (PreH40 : (retval <> 0)) (PreH41 : (original = a)) (PreH42 : (n_pre = (Zlength (original)))) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
|--
  “ (Spec a n_pre ) ”
  &&  (IntArray.full input_pre n_pre a )
.

Definition solver_partial_solve_wit_1_pure := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (original: (@list Z)) (PreH1 : (original = a)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "a" ) )) # Ptr  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full input_pre n_pre original )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (original: (@list Z)) (PreH1 : (original = a)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre original )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.seg a_2 0 i copied )
  **  (IntArray.undef_seg a_2 i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((input_pre + (i * sizeof(INT)))) # Int  |-> (Znth i original 0))
  **  (IntArray.missing_i input_pre i 0 n_pre original )
  **  (IntArray.seg a_2 0 i copied )
  **  (IntArray.undef_seg a_2 i n_pre )
.

Definition solver_partial_solve_wit_3 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.seg a_2 0 i copied )
  **  (IntArray.undef_seg a_2 i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((a_2 + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.seg a_2 0 i copied )
.

Definition solver_partial_solve_wit_4 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.seg a_2 0 (i + 1 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
  **  (IntArray.full input_pre n_pre original )
|--
  “ (i < n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((a_2 + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) 0))
  **  (IntArray.missing_i a_2 i 0 (i + 1 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
  **  (IntArray.full input_pre n_pre original )
.

Definition solver_partial_solve_wit_5 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (copied: (@list Z)) (mx: Z) (i: Z) (a_2: Z) (PreH1 : ((Znth (i - 0 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) 0) > mx)) (PreH2 : (i < n_pre)) (PreH3 : (a_2 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= mx)) (PreH11 : (mx <= 1000000000)) (PreH12 : (CopyMaxState original copied i mx )) (PreH13 : (retval <> 0)) (PreH14 : (original = a)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.seg a_2 0 (i + 1 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
  **  (IntArray.full input_pre n_pre original )
|--
  “ ((Znth (i - 0 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) 0) > mx) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((a_2 + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) 0))
  **  (IntArray.missing_i a_2 i 0 (i + 1 ) (app (copied) ((cons ((Znth i original 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg a_2 (i + 1 ) n_pre )
  **  (IntArray.full input_pre n_pre original )
.

Definition solver_partial_solve_wit_6_pure := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_2)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.seg a_2 0 finished_i copied )
  **  (IntArray.undef_seg a_2 finished_i n_pre )
  **  ((( &( "all" ) )) # Int64  |-> 1)
|--
  “ (finished_i = n_pre) ” 
  &&  “ ((Zlength (copied)) = finished_i) ”
) \/
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (1 <= INT64_MAX)) (PreH2 : (1 >= INT64_MIN)) (PreH3 : (mx <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (mx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (finished_i >= n_pre)) (PreH8 : (a_2 <> 0)) (PreH9 : (n_pre = (Zlength (original)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH13 : (0 <= finished_i)) (PreH14 : (finished_i <= n_pre)) (PreH15 : (0 <= mx)) (PreH16 : (mx <= 1000000000)) (PreH17 : (CopyMaxState original copied finished_i mx )) (PreH18 : (retval <> 0)) (PreH19 : (original = a)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_2)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.seg a_2 0 finished_i copied )
  **  ((( &( "all" ) )) # Int64  |-> 1)
|--
  “ ((Zlength (copied)) = finished_i) ”
).

Definition solver_partial_solve_wit_6_pure_split_goal_1 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (1 <= INT64_MAX)) (PreH2 : (1 >= INT64_MIN)) (PreH3 : (mx <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (mx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (finished_i >= n_pre)) (PreH8 : (a_2 <> 0)) (PreH9 : (n_pre = (Zlength (original)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH13 : (0 <= finished_i)) (PreH14 : (finished_i <= n_pre)) (PreH15 : (0 <= mx)) (PreH16 : (mx <= 1000000000)) (PreH17 : (CopyMaxState original copied finished_i mx )) (PreH18 : (retval <> 0)) (PreH19 : (original = a)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_2)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.seg a_2 0 finished_i copied )
  **  ((( &( "all" ) )) # Int64  |-> 1)
|--
  “ ((Zlength (copied)) = finished_i) ”
.

Definition solver_partial_solve_wit_6_aux := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (PreH1 : (finished_i >= n_pre)) (PreH2 : (a_2 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH7 : (0 <= finished_i)) (PreH8 : (finished_i <= n_pre)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (CopyMaxState original copied finished_i mx )) (PreH12 : (retval <> 0)) (PreH13 : (original = a)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.seg a_2 0 finished_i copied )
  **  (IntArray.undef_seg a_2 finished_i n_pre )
|--
  “ (finished_i = n_pre) ” 
  &&  “ ((Zlength (copied)) = finished_i) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.seg a_2 0 finished_i copied )
  **  (IntArray.full input_pre n_pre original )
.

Definition solver_partial_solve_wit_6 := solver_partial_solve_wit_6_pure -> solver_partial_solve_wit_6_aux.

Definition solver_partial_solve_wit_7 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_3 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH9 : (1 <= mx_2)) (PreH10 : (mx_2 <= 1000000000)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= all)) (PreH14 : (all <= (mx_2 + 1 ))) (PreH15 : (CopyMaxState original copied n_pre mx_2 )) (PreH16 : (LcmPrefixState copied i mx_2 all )) (PreH17 : (finished_i >= n_pre)) (PreH18 : (a_2 <> 0)) (PreH19 : (n_pre = (Zlength (original)))) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 2000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH23 : (0 <= finished_i)) (PreH24 : (finished_i <= n_pre)) (PreH25 : (0 <= mx)) (PreH26 : (mx <= 1000000000)) (PreH27 : (CopyMaxState original copied finished_i mx )) (PreH28 : (retval <> 0)) (PreH29 : (original = a)) (PreH30 : (n_pre = (Zlength (original)))) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre copied )
|--
  “ (i < n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((a_3 + (i * sizeof(INT)))) # Int  |-> (Znth i copied 0))
  **  (IntArray.missing_i a_3 i 0 n_pre copied )
  **  (IntArray.full input_pre n_pre original )
.

Definition solver_partial_solve_wit_8_pure := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx_2: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx: Z) (a_3: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_3 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH9 : (1 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= all)) (PreH14 : (all <= (mx + 1 ))) (PreH15 : (CopyMaxState original copied n_pre mx )) (PreH16 : (LcmPrefixState copied i mx all )) (PreH17 : (finished_i >= n_pre)) (PreH18 : (a_2 <> 0)) (PreH19 : (n_pre = (Zlength (original)))) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 2000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH23 : (0 <= finished_i)) (PreH24 : (finished_i <= n_pre)) (PreH25 : (0 <= mx_2)) (PreH26 : (mx_2 <= 1000000000)) (PreH27 : (CopyMaxState original copied finished_i mx_2 )) (PreH28 : (retval <> 0)) (PreH29 : (original = a)) (PreH30 : (n_pre = (Zlength (original)))) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_3 n_pre copied )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_3)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "all" ) )) # Int64  |-> all)
  **  (IntArray.full input_pre n_pre original )
|--
  “ (1 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx + 1 )) ” 
  &&  “ (1 <= (Znth i copied 0)) ” 
  &&  “ ((Znth i copied 0) <= mx) ”
) \/
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx_2: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx: Z) (a_3: Z) (PreH1 : (all <= INT64_MAX)) (PreH2 : (all >= INT64_MIN)) (PreH3 : (i <= INT_MAX)) (PreH4 : (mx <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (mx >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (a_3 <> 0)) (PreH11 : (n_pre = (Zlength (original)))) (PreH12 : ((Zlength (copied)) = n_pre)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 2000)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH17 : (1 <= mx)) (PreH18 : (mx <= 1000000000)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (1 <= all)) (PreH22 : (all <= (mx + 1 ))) (PreH23 : (CopyMaxState original copied n_pre mx )) (PreH24 : (LcmPrefixState copied i mx all )) (PreH25 : (finished_i >= n_pre)) (PreH26 : (a_2 <> 0)) (PreH27 : (n_pre = (Zlength (original)))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH31 : (0 <= finished_i)) (PreH32 : (finished_i <= n_pre)) (PreH33 : (0 <= mx_2)) (PreH34 : (mx_2 <= 1000000000)) (PreH35 : (CopyMaxState original copied finished_i mx_2 )) (PreH36 : (retval <> 0)) (PreH37 : (original = a)) (PreH38 : (n_pre = (Zlength (original)))) (PreH39 : (1 <= n_pre)) (PreH40 : (n_pre <= 2000)) (PreH41 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_3 n_pre copied )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_3)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "all" ) )) # Int64  |-> all)
  **  (IntArray.full input_pre n_pre original )
|--
  “ ((Znth i copied 0) <= mx) ”
).

Definition solver_partial_solve_wit_8_pure_split_goal_1 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx_2: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx: Z) (a_3: Z) (PreH1 : (all <= INT64_MAX)) (PreH2 : (all >= INT64_MIN)) (PreH3 : (i <= INT_MAX)) (PreH4 : (mx <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (mx >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (a_3 <> 0)) (PreH11 : (n_pre = (Zlength (original)))) (PreH12 : ((Zlength (copied)) = n_pre)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 2000)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH17 : (1 <= mx)) (PreH18 : (mx <= 1000000000)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (1 <= all)) (PreH22 : (all <= (mx + 1 ))) (PreH23 : (CopyMaxState original copied n_pre mx )) (PreH24 : (LcmPrefixState copied i mx all )) (PreH25 : (finished_i >= n_pre)) (PreH26 : (a_2 <> 0)) (PreH27 : (n_pre = (Zlength (original)))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH31 : (0 <= finished_i)) (PreH32 : (finished_i <= n_pre)) (PreH33 : (0 <= mx_2)) (PreH34 : (mx_2 <= 1000000000)) (PreH35 : (CopyMaxState original copied finished_i mx_2 )) (PreH36 : (retval <> 0)) (PreH37 : (original = a)) (PreH38 : (n_pre = (Zlength (original)))) (PreH39 : (1 <= n_pre)) (PreH40 : (n_pre <= 2000)) (PreH41 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_3 n_pre copied )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_3)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "all" ) )) # Int64  |-> all)
  **  (IntArray.full input_pre n_pre original )
|--
  “ ((Znth i copied 0) <= mx) ”
.

Definition solver_partial_solve_wit_8_aux := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx_2: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx: Z) (a_3: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_3 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH9 : (1 <= mx)) (PreH10 : (mx <= 1000000000)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= all)) (PreH14 : (all <= (mx + 1 ))) (PreH15 : (CopyMaxState original copied n_pre mx )) (PreH16 : (LcmPrefixState copied i mx all )) (PreH17 : (finished_i >= n_pre)) (PreH18 : (a_2 <> 0)) (PreH19 : (n_pre = (Zlength (original)))) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 2000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH23 : (0 <= finished_i)) (PreH24 : (finished_i <= n_pre)) (PreH25 : (0 <= mx_2)) (PreH26 : (mx_2 <= 1000000000)) (PreH27 : (CopyMaxState original copied finished_i mx_2 )) (PreH28 : (retval <> 0)) (PreH29 : (original = a)) (PreH30 : (n_pre = (Zlength (original)))) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_3 n_pre copied )
  **  (IntArray.full input_pre n_pre original )
|--
  “ (1 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx + 1 )) ” 
  &&  “ (1 <= (Znth i copied 0)) ” 
  &&  “ ((Znth i copied 0) <= mx) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx ) ” 
  &&  “ (LcmPrefixState copied i mx all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx_2 ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full a_3 n_pre copied )
  **  (IntArray.full input_pre n_pre original )
.

Definition solver_partial_solve_wit_8 := solver_partial_solve_wit_8_pure -> solver_partial_solve_wit_8_aux.

Definition solver_partial_solve_wit_9 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (PreH1 : (a_3 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (copied)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= mx_2)) (PreH7 : (mx_2 <= 1000000000)) (PreH8 : (all <> mx_2)) (PreH9 : (CopyMaxState original copied n_pre mx_2 )) (PreH10 : (LcmPrefixState copied n_pre mx_2 all )) (PreH11 : (Spec original n_pre )) (PreH12 : (all <> mx_2)) (PreH13 : (i >= n_pre)) (PreH14 : (a_3 <> 0)) (PreH15 : (n_pre = (Zlength (original)))) (PreH16 : ((Zlength (copied)) = n_pre)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH20 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH21 : (1 <= mx_2)) (PreH22 : (mx_2 <= 1000000000)) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (1 <= all)) (PreH26 : (all <= (mx_2 + 1 ))) (PreH27 : (CopyMaxState original copied n_pre mx_2 )) (PreH28 : (LcmPrefixState copied i mx_2 all )) (PreH29 : (finished_i >= n_pre)) (PreH30 : (a_2 <> 0)) (PreH31 : (n_pre = (Zlength (original)))) (PreH32 : (1 <= n_pre)) (PreH33 : (n_pre <= 2000)) (PreH34 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH35 : (0 <= finished_i)) (PreH36 : (finished_i <= n_pre)) (PreH37 : (0 <= mx)) (PreH38 : (mx <= 1000000000)) (PreH39 : (CopyMaxState original copied finished_i mx )) (PreH40 : (retval <> 0)) (PreH41 : (original = a)) (PreH42 : (n_pre = (Zlength (original)))) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre copied )
|--
  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (all <> mx_2) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_2 all ) ” 
  &&  “ (Spec original n_pre ) ” 
  &&  “ (all <> mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full a_3 (Zlength (a)) copied )
  **  (IntArray.full input_pre n_pre original )
.

Definition solver_partial_solve_wit_10_pure := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (PreH1 : (all = mx_2)) (PreH2 : (i >= n_pre)) (PreH3 : (a_3 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH10 : (1 <= mx_2)) (PreH11 : (mx_2 <= 1000000000)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= all)) (PreH15 : (all <= (mx_2 + 1 ))) (PreH16 : (CopyMaxState original copied n_pre mx_2 )) (PreH17 : (LcmPrefixState copied i mx_2 all )) (PreH18 : (finished_i >= n_pre)) (PreH19 : (a_2 <> 0)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH24 : (0 <= finished_i)) (PreH25 : (finished_i <= n_pre)) (PreH26 : (0 <= mx)) (PreH27 : (mx <= 1000000000)) (PreH28 : (CopyMaxState original copied finished_i mx )) (PreH29 : (retval <> 0)) (PreH30 : (original = a)) (PreH31 : (n_pre = (Zlength (original)))) (PreH32 : (1 <= n_pre)) (PreH33 : (n_pre <= 2000)) (PreH34 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_3)
  **  ((( &( "mx" ) )) # Int  |-> mx_2)
  **  ((( &( "all" ) )) # Int64  |-> all)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre copied )
|--
  “ (n_pre = (Zlength (copied))) ” 
  &&  “ (sizeof(INT) = sizeof(INT)) ”
.

Definition solver_partial_solve_wit_10_aux := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (PreH1 : (all = mx_2)) (PreH2 : (i >= n_pre)) (PreH3 : (a_3 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH10 : (1 <= mx_2)) (PreH11 : (mx_2 <= 1000000000)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= all)) (PreH15 : (all <= (mx_2 + 1 ))) (PreH16 : (CopyMaxState original copied n_pre mx_2 )) (PreH17 : (LcmPrefixState copied i mx_2 all )) (PreH18 : (finished_i >= n_pre)) (PreH19 : (a_2 <> 0)) (PreH20 : (n_pre = (Zlength (original)))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH24 : (0 <= finished_i)) (PreH25 : (finished_i <= n_pre)) (PreH26 : (0 <= mx)) (PreH27 : (mx <= 1000000000)) (PreH28 : (CopyMaxState original copied finished_i mx )) (PreH29 : (retval <> 0)) (PreH30 : (original = a)) (PreH31 : (n_pre = (Zlength (original)))) (PreH32 : (1 <= n_pre)) (PreH33 : (n_pre <= 2000)) (PreH34 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_3 n_pre copied )
|--
  “ (n_pre = (Zlength (copied))) ” 
  &&  “ (sizeof(INT) = sizeof(INT)) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full a_3 n_pre copied )
  **  (IntArray.full input_pre n_pre original )
.

Definition solver_partial_solve_wit_10 := solver_partial_solve_wit_10_pure -> solver_partial_solve_wit_10_aux.

Definition solver_partial_solve_wit_11 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (PreH1 : (z < 2)) (PreH2 : (a_5 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_4)) (PreH9 : (mx_4 <= 1000000000)) (PreH10 : (all_3 = mx_4)) (PreH11 : (1 <= q_2)) (PreH12 : (q_2 <= 31623)) (PreH13 : ((q_2 * q_2 ) <= mx_4)) (PreH14 : ((mx_4 % ( q_2 ) ) = 0)) (PreH15 : (0 <= z)) (PreH16 : (z <= 2)) (PreH17 : (0 <= ans_2)) (PreH18 : (ans_2 <= n_pre)) (PreH19 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH20 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH21 : (CopyMaxState original copied n_pre mx_4 )) (PreH22 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH23 : (Permutation copied sorted )) (PreH24 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH25 : ((mx_3 % ( q ) ) = 0)) (PreH26 : ((q * q ) <= mx_3)) (PreH27 : (a_4 <> 0)) (PreH28 : (n_pre = (Zlength (original)))) (PreH29 : ((Zlength (copied)) = n_pre)) (PreH30 : ((Zlength (sorted)) = n_pre)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= mx_3)) (PreH34 : (mx_3 <= 1000000000)) (PreH35 : (all_2 = mx_3)) (PreH36 : (1 <= q)) (PreH37 : (q <= 31624)) (PreH38 : (0 <= ans)) (PreH39 : (ans <= n_pre)) (PreH40 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH41 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH42 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre mx_3 )) (PreH44 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH45 : (Permutation copied sorted )) (PreH46 : (DivisorBestState original mx_3 q 0 ans )) (PreH47 : (a_3 <> 0)) (PreH48 : (n_pre = (Zlength (original)))) (PreH49 : ((Zlength (copied)) = n_pre)) (PreH50 : ((Zlength (sorted)) = n_pre)) (PreH51 : (1 <= n_pre)) (PreH52 : (n_pre <= 2000)) (PreH53 : (1 <= all)) (PreH54 : (all <= 1000000000)) (PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH56 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre all )) (PreH58 : (LcmPrefixState copied n_pre all all )) (PreH59 : (Permutation copied sorted )) (PreH60 : (Permutation copied sorted )) (PreH61 : ((Zlength (sorted)) = n_pre)) (PreH62 : (all = mx_2)) (PreH63 : (i >= n_pre)) (PreH64 : (a_3 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH70 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH71 : (1 <= mx_2)) (PreH72 : (mx_2 <= 1000000000)) (PreH73 : (0 <= i)) (PreH74 : (i <= n_pre)) (PreH75 : (1 <= all)) (PreH76 : (all <= (mx_2 + 1 ))) (PreH77 : (CopyMaxState original copied n_pre mx_2 )) (PreH78 : (LcmPrefixState copied i mx_2 all )) (PreH79 : (finished_i >= n_pre)) (PreH80 : (a_2 <> 0)) (PreH81 : (n_pre = (Zlength (original)))) (PreH82 : (1 <= n_pre)) (PreH83 : (n_pre <= 2000)) (PreH84 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH85 : (0 <= finished_i)) (PreH86 : (finished_i <= n_pre)) (PreH87 : (0 <= mx)) (PreH88 : (mx <= 1000000000)) (PreH89 : (CopyMaxState original copied finished_i mx )) (PreH90 : (retval <> 0)) (PreH91 : (original = a)) (PreH92 : (n_pre = (Zlength (original)))) (PreH93 : (1 <= n_pre)) (PreH94 : (n_pre <= 2000)) (PreH95 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
|--
  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((( &( "ds" ) ) + (z * sizeof(INT)))) # Int  |-> (Znth z (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) 0))
  **  (IntArray.missing_i ( &( "ds" ) ) z 0 2 (cons (q_2) ((cons ((mx_4 ÷ q_2 )) ((@nil Z))))) )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_5 n_pre sorted )
.

Definition solver_partial_solve_wit_12 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (a_6 <> 0)) (PreH3 : (n_pre = (Zlength (original)))) (PreH4 : ((Zlength (copied)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= mx_5)) (PreH9 : (mx_5 <= 1000000000)) (PreH10 : (all_4 = mx_5)) (PreH11 : (1 <= q_3)) (PreH12 : (q_3 <= 31623)) (PreH13 : ((q_3 * q_3 ) <= mx_5)) (PreH14 : ((mx_5 % ( q_3 ) ) = 0)) (PreH15 : (0 <= z_2)) (PreH16 : (z_2 < 2)) (PreH17 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH18 : (1 <= d)) (PreH19 : (d <= mx_5)) (PreH20 : (0 <= ans_3)) (PreH21 : (ans_3 <= n_pre)) (PreH22 : (0 <= i_2)) (PreH23 : (i_2 <= n_pre)) (PreH24 : (0 <= present)) (PreH25 : (present <= 1)) (PreH26 : (0 <= count)) (PreH27 : (count <= i_2)) (PreH28 : (1 <= l)) (PreH29 : (l <= (d + 1 ))) (PreH30 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH31 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH32 : (CopyMaxState original copied n_pre mx_5 )) (PreH33 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH34 : (Permutation copied sorted )) (PreH35 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH36 : (DivisorScanState sorted d i_2 present count l )) (PreH37 : (z < 2)) (PreH38 : (a_5 <> 0)) (PreH39 : (n_pre = (Zlength (original)))) (PreH40 : ((Zlength (copied)) = n_pre)) (PreH41 : ((Zlength (sorted)) = n_pre)) (PreH42 : (1 <= n_pre)) (PreH43 : (n_pre <= 2000)) (PreH44 : (1 <= mx_4)) (PreH45 : (mx_4 <= 1000000000)) (PreH46 : (all_3 = mx_4)) (PreH47 : (1 <= q_2)) (PreH48 : (q_2 <= 31623)) (PreH49 : ((q_2 * q_2 ) <= mx_4)) (PreH50 : ((mx_4 % ( q_2 ) ) = 0)) (PreH51 : (0 <= z)) (PreH52 : (z <= 2)) (PreH53 : (0 <= ans_2)) (PreH54 : (ans_2 <= n_pre)) (PreH55 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH56 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH57 : (CopyMaxState original copied n_pre mx_4 )) (PreH58 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH59 : (Permutation copied sorted )) (PreH60 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH61 : ((mx_3 % ( q ) ) = 0)) (PreH62 : ((q * q ) <= mx_3)) (PreH63 : (a_4 <> 0)) (PreH64 : (n_pre = (Zlength (original)))) (PreH65 : ((Zlength (copied)) = n_pre)) (PreH66 : ((Zlength (sorted)) = n_pre)) (PreH67 : (1 <= n_pre)) (PreH68 : (n_pre <= 2000)) (PreH69 : (1 <= mx_3)) (PreH70 : (mx_3 <= 1000000000)) (PreH71 : (all_2 = mx_3)) (PreH72 : (1 <= q)) (PreH73 : (q <= 31624)) (PreH74 : (0 <= ans)) (PreH75 : (ans <= n_pre)) (PreH76 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH77 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH78 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH79 : (CopyMaxState original copied n_pre mx_3 )) (PreH80 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH81 : (Permutation copied sorted )) (PreH82 : (DivisorBestState original mx_3 q 0 ans )) (PreH83 : (a_3 <> 0)) (PreH84 : (n_pre = (Zlength (original)))) (PreH85 : ((Zlength (copied)) = n_pre)) (PreH86 : ((Zlength (sorted)) = n_pre)) (PreH87 : (1 <= n_pre)) (PreH88 : (n_pre <= 2000)) (PreH89 : (1 <= all)) (PreH90 : (all <= 1000000000)) (PreH91 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH92 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH93 : (CopyMaxState original copied n_pre all )) (PreH94 : (LcmPrefixState copied n_pre all all )) (PreH95 : (Permutation copied sorted )) (PreH96 : (Permutation copied sorted )) (PreH97 : ((Zlength (sorted)) = n_pre)) (PreH98 : (all = mx_2)) (PreH99 : (i >= n_pre)) (PreH100 : (a_3 <> 0)) (PreH101 : (n_pre = (Zlength (original)))) (PreH102 : ((Zlength (copied)) = n_pre)) (PreH103 : (1 <= n_pre)) (PreH104 : (n_pre <= 2000)) (PreH105 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH106 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH107 : (1 <= mx_2)) (PreH108 : (mx_2 <= 1000000000)) (PreH109 : (0 <= i)) (PreH110 : (i <= n_pre)) (PreH111 : (1 <= all)) (PreH112 : (all <= (mx_2 + 1 ))) (PreH113 : (CopyMaxState original copied n_pre mx_2 )) (PreH114 : (LcmPrefixState copied i mx_2 all )) (PreH115 : (finished_i >= n_pre)) (PreH116 : (a_2 <> 0)) (PreH117 : (n_pre = (Zlength (original)))) (PreH118 : (1 <= n_pre)) (PreH119 : (n_pre <= 2000)) (PreH120 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH121 : (0 <= finished_i)) (PreH122 : (finished_i <= n_pre)) (PreH123 : (0 <= mx)) (PreH124 : (mx <= 1000000000)) (PreH125 : (CopyMaxState original copied finished_i mx )) (PreH126 : (retval <> 0)) (PreH127 : (original = a)) (PreH128 : (n_pre = (Zlength (original)))) (PreH129 : (1 <= n_pre)) (PreH130 : (n_pre <= 2000)) (PreH131 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (i_2 < n_pre) ” 
  &&  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (0 <= present) ” 
  &&  “ (present <= 1) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i_2) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d i_2 present count l ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((a_6 + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 sorted 0))
  **  (IntArray.missing_i a_6 i_2 0 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_13 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((Znth i_2 sorted 0) = d)) (PreH2 : (i_2 < n_pre)) (PreH3 : (a_6 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_5)) (PreH10 : (mx_5 <= 1000000000)) (PreH11 : (all_4 = mx_5)) (PreH12 : (1 <= q_3)) (PreH13 : (q_3 <= 31623)) (PreH14 : ((q_3 * q_3 ) <= mx_5)) (PreH15 : ((mx_5 % ( q_3 ) ) = 0)) (PreH16 : (0 <= z_2)) (PreH17 : (z_2 < 2)) (PreH18 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_5)) (PreH21 : (0 <= ans_3)) (PreH22 : (ans_3 <= n_pre)) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i_2)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_5 )) (PreH34 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH37 : (DivisorScanState sorted d i_2 present count l )) (PreH38 : (z < 2)) (PreH39 : (a_5 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_4)) (PreH46 : (mx_4 <= 1000000000)) (PreH47 : (all_3 = mx_4)) (PreH48 : (1 <= q_2)) (PreH49 : (q_2 <= 31623)) (PreH50 : ((q_2 * q_2 ) <= mx_4)) (PreH51 : ((mx_4 % ( q_2 ) ) = 0)) (PreH52 : (0 <= z)) (PreH53 : (z <= 2)) (PreH54 : (0 <= ans_2)) (PreH55 : (ans_2 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_4 )) (PreH59 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i)) (PreH111 : (i <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((Znth i_2 sorted 0) = d) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (0 <= present) ” 
  &&  “ (present <= 1) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i_2) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d i_2 present count l ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((a_6 + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 sorted 0))
  **  (IntArray.missing_i a_6 i_2 0 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_14 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((Znth i_2 sorted 0) <> d)) (PreH2 : (i_2 < n_pre)) (PreH3 : (a_6 <> 0)) (PreH4 : (n_pre = (Zlength (original)))) (PreH5 : ((Zlength (copied)) = n_pre)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2000)) (PreH9 : (1 <= mx_5)) (PreH10 : (mx_5 <= 1000000000)) (PreH11 : (all_4 = mx_5)) (PreH12 : (1 <= q_3)) (PreH13 : (q_3 <= 31623)) (PreH14 : ((q_3 * q_3 ) <= mx_5)) (PreH15 : ((mx_5 % ( q_3 ) ) = 0)) (PreH16 : (0 <= z_2)) (PreH17 : (z_2 < 2)) (PreH18 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH19 : (1 <= d)) (PreH20 : (d <= mx_5)) (PreH21 : (0 <= ans_3)) (PreH22 : (ans_3 <= n_pre)) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 <= n_pre)) (PreH25 : (0 <= present)) (PreH26 : (present <= 1)) (PreH27 : (0 <= count)) (PreH28 : (count <= i_2)) (PreH29 : (1 <= l)) (PreH30 : (l <= (d + 1 ))) (PreH31 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH32 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH33 : (CopyMaxState original copied n_pre mx_5 )) (PreH34 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH35 : (Permutation copied sorted )) (PreH36 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH37 : (DivisorScanState sorted d i_2 present count l )) (PreH38 : (z < 2)) (PreH39 : (a_5 <> 0)) (PreH40 : (n_pre = (Zlength (original)))) (PreH41 : ((Zlength (copied)) = n_pre)) (PreH42 : ((Zlength (sorted)) = n_pre)) (PreH43 : (1 <= n_pre)) (PreH44 : (n_pre <= 2000)) (PreH45 : (1 <= mx_4)) (PreH46 : (mx_4 <= 1000000000)) (PreH47 : (all_3 = mx_4)) (PreH48 : (1 <= q_2)) (PreH49 : (q_2 <= 31623)) (PreH50 : ((q_2 * q_2 ) <= mx_4)) (PreH51 : ((mx_4 % ( q_2 ) ) = 0)) (PreH52 : (0 <= z)) (PreH53 : (z <= 2)) (PreH54 : (0 <= ans_2)) (PreH55 : (ans_2 <= n_pre)) (PreH56 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH57 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH58 : (CopyMaxState original copied n_pre mx_4 )) (PreH59 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH60 : (Permutation copied sorted )) (PreH61 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH62 : ((mx_3 % ( q ) ) = 0)) (PreH63 : ((q * q ) <= mx_3)) (PreH64 : (a_4 <> 0)) (PreH65 : (n_pre = (Zlength (original)))) (PreH66 : ((Zlength (copied)) = n_pre)) (PreH67 : ((Zlength (sorted)) = n_pre)) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : (1 <= mx_3)) (PreH71 : (mx_3 <= 1000000000)) (PreH72 : (all_2 = mx_3)) (PreH73 : (1 <= q)) (PreH74 : (q <= 31624)) (PreH75 : (0 <= ans)) (PreH76 : (ans <= n_pre)) (PreH77 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH78 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH79 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH80 : (CopyMaxState original copied n_pre mx_3 )) (PreH81 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH82 : (Permutation copied sorted )) (PreH83 : (DivisorBestState original mx_3 q 0 ans )) (PreH84 : (a_3 <> 0)) (PreH85 : (n_pre = (Zlength (original)))) (PreH86 : ((Zlength (copied)) = n_pre)) (PreH87 : ((Zlength (sorted)) = n_pre)) (PreH88 : (1 <= n_pre)) (PreH89 : (n_pre <= 2000)) (PreH90 : (1 <= all)) (PreH91 : (all <= 1000000000)) (PreH92 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH93 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH94 : (CopyMaxState original copied n_pre all )) (PreH95 : (LcmPrefixState copied n_pre all all )) (PreH96 : (Permutation copied sorted )) (PreH97 : (Permutation copied sorted )) (PreH98 : ((Zlength (sorted)) = n_pre)) (PreH99 : (all = mx_2)) (PreH100 : (i >= n_pre)) (PreH101 : (a_3 <> 0)) (PreH102 : (n_pre = (Zlength (original)))) (PreH103 : ((Zlength (copied)) = n_pre)) (PreH104 : (1 <= n_pre)) (PreH105 : (n_pre <= 2000)) (PreH106 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH107 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH108 : (1 <= mx_2)) (PreH109 : (mx_2 <= 1000000000)) (PreH110 : (0 <= i)) (PreH111 : (i <= n_pre)) (PreH112 : (1 <= all)) (PreH113 : (all <= (mx_2 + 1 ))) (PreH114 : (CopyMaxState original copied n_pre mx_2 )) (PreH115 : (LcmPrefixState copied i mx_2 all )) (PreH116 : (finished_i >= n_pre)) (PreH117 : (a_2 <> 0)) (PreH118 : (n_pre = (Zlength (original)))) (PreH119 : (1 <= n_pre)) (PreH120 : (n_pre <= 2000)) (PreH121 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH122 : (0 <= finished_i)) (PreH123 : (finished_i <= n_pre)) (PreH124 : (0 <= mx)) (PreH125 : (mx <= 1000000000)) (PreH126 : (CopyMaxState original copied finished_i mx )) (PreH127 : (retval <> 0)) (PreH128 : (original = a)) (PreH129 : (n_pre = (Zlength (original)))) (PreH130 : (1 <= n_pre)) (PreH131 : (n_pre <= 2000)) (PreH132 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((Znth i_2 sorted 0) <> d) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (0 <= present) ” 
  &&  “ (present <= 1) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i_2) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d i_2 present count l ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((a_6 + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 sorted 0))
  **  (IntArray.missing_i a_6 i_2 0 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_15 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i_2 sorted 0) ) ) = 0)) (PreH2 : ((Znth i_2 sorted 0) = d)) (PreH3 : (i_2 < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((d % ( (Znth i_2 sorted 0) ) ) = 0) ” 
  &&  “ ((Znth i_2 sorted 0) = d) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (0 <= present) ” 
  &&  “ (present <= 1) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i_2) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d i_2 present count l ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((a_6 + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 sorted 0))
  **  (IntArray.missing_i a_6 i_2 0 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_16_pure := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i sorted 0) ) ) = 0)) (PreH2 : ((Znth i sorted 0) = d)) (PreH3 : (i < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i_2 >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i_2)) (PreH112 : (i_2 <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i_2 mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "present" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (1 <= d) ” 
  &&  “ (d <= 1000000000) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ (1 <= (Znth i sorted 0)) ” 
  &&  “ ((Znth i sorted 0) <= d) ”
.

Definition solver_partial_solve_wit_16_aux := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i sorted 0) ) ) = 0)) (PreH2 : ((Znth i sorted 0) = d)) (PreH3 : (i < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i_2 >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i_2)) (PreH112 : (i_2 <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i_2 mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (1 <= d) ” 
  &&  “ (d <= 1000000000) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ (1 <= (Znth i sorted 0)) ” 
  &&  “ ((Znth i sorted 0) <= d) ” 
  &&  “ ((d % ( (Znth i sorted 0) ) ) = 0) ” 
  &&  “ ((Znth i sorted 0) = d) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= present) ” 
  &&  “ (present <= 1) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d i present count l ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i_2 >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i_2 mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_16 := solver_partial_solve_wit_16_pure -> solver_partial_solve_wit_16_aux.

Definition solver_partial_solve_wit_17 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i_2: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i_2 sorted 0) ) ) = 0)) (PreH2 : ((Znth i_2 sorted 0) <> d)) (PreH3 : (i_2 < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i_2)) (PreH25 : (i_2 <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i_2)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i_2 present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i)) (PreH112 : (i <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((d % ( (Znth i_2 sorted 0) ) ) = 0) ” 
  &&  “ ((Znth i_2 sorted 0) <> d) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (0 <= present) ” 
  &&  “ (present <= 1) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i_2) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d i_2 present count l ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (((a_6 + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 sorted 0))
  **  (IntArray.missing_i a_6 i_2 0 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_18_pure := 
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i sorted 0) ) ) = 0)) (PreH2 : ((Znth i sorted 0) <> d)) (PreH3 : (i < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i_2 >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i_2)) (PreH112 : (i_2 <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i_2 mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "present" ) )) # Int  |-> present)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (1 <= d) ” 
  &&  “ (d <= 1000000000) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ (1 <= (Znth i sorted 0)) ” 
  &&  “ ((Znth i sorted 0) <= d) ”
) \/
(
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : (l <= INT64_MAX)) (PreH2 : (all_4 <= INT64_MAX)) (PreH3 : (l >= INT64_MIN)) (PreH4 : (all_4 >= INT64_MIN)) (PreH5 : ((count + 1 ) <= INT_MAX)) (PreH6 : (present <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (ans_3 <= INT_MAX)) (PreH9 : (d <= INT_MAX)) (PreH10 : (z_2 <= INT_MAX)) (PreH11 : (q_3 <= INT_MAX)) (PreH12 : (mx_5 <= INT_MAX)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : ((count + 1 ) >= INT_MIN)) (PreH15 : (present >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (ans_3 >= INT_MIN)) (PreH18 : (d >= INT_MIN)) (PreH19 : (z_2 >= INT_MIN)) (PreH20 : (q_3 >= INT_MIN)) (PreH21 : (mx_5 >= INT_MIN)) (PreH22 : (n_pre >= INT_MIN)) (PreH23 : ((d % ( (Znth i sorted 0) ) ) = 0)) (PreH24 : ((Znth i sorted 0) <> d)) (PreH25 : (i < n_pre)) (PreH26 : (a_6 <> 0)) (PreH27 : (n_pre = (Zlength (original)))) (PreH28 : ((Zlength (copied)) = n_pre)) (PreH29 : ((Zlength (sorted)) = n_pre)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 2000)) (PreH32 : (1 <= mx_5)) (PreH33 : (mx_5 <= 1000000000)) (PreH34 : (all_4 = mx_5)) (PreH35 : (1 <= q_3)) (PreH36 : (q_3 <= 31623)) (PreH37 : ((q_3 * q_3 ) <= mx_5)) (PreH38 : ((mx_5 % ( q_3 ) ) = 0)) (PreH39 : (0 <= z_2)) (PreH40 : (z_2 < 2)) (PreH41 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH42 : (1 <= d)) (PreH43 : (d <= mx_5)) (PreH44 : (0 <= ans_3)) (PreH45 : (ans_3 <= n_pre)) (PreH46 : (0 <= i)) (PreH47 : (i <= n_pre)) (PreH48 : (0 <= present)) (PreH49 : (present <= 1)) (PreH50 : (0 <= count)) (PreH51 : (count <= i)) (PreH52 : (1 <= l)) (PreH53 : (l <= (d + 1 ))) (PreH54 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH55 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH56 : (CopyMaxState original copied n_pre mx_5 )) (PreH57 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH58 : (Permutation copied sorted )) (PreH59 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH60 : (DivisorScanState sorted d i present count l )) (PreH61 : (z < 2)) (PreH62 : (a_5 <> 0)) (PreH63 : (n_pre = (Zlength (original)))) (PreH64 : ((Zlength (copied)) = n_pre)) (PreH65 : ((Zlength (sorted)) = n_pre)) (PreH66 : (1 <= n_pre)) (PreH67 : (n_pre <= 2000)) (PreH68 : (1 <= mx_4)) (PreH69 : (mx_4 <= 1000000000)) (PreH70 : (all_3 = mx_4)) (PreH71 : (1 <= q_2)) (PreH72 : (q_2 <= 31623)) (PreH73 : ((q_2 * q_2 ) <= mx_4)) (PreH74 : ((mx_4 % ( q_2 ) ) = 0)) (PreH75 : (0 <= z)) (PreH76 : (z <= 2)) (PreH77 : (0 <= ans_2)) (PreH78 : (ans_2 <= n_pre)) (PreH79 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH80 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_4 )) (PreH82 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH85 : ((mx_3 % ( q ) ) = 0)) (PreH86 : ((q * q ) <= mx_3)) (PreH87 : (a_4 <> 0)) (PreH88 : (n_pre = (Zlength (original)))) (PreH89 : ((Zlength (copied)) = n_pre)) (PreH90 : ((Zlength (sorted)) = n_pre)) (PreH91 : (1 <= n_pre)) (PreH92 : (n_pre <= 2000)) (PreH93 : (1 <= mx_3)) (PreH94 : (mx_3 <= 1000000000)) (PreH95 : (all_2 = mx_3)) (PreH96 : (1 <= q)) (PreH97 : (q <= 31624)) (PreH98 : (0 <= ans)) (PreH99 : (ans <= n_pre)) (PreH100 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH101 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH102 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH103 : (CopyMaxState original copied n_pre mx_3 )) (PreH104 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH105 : (Permutation copied sorted )) (PreH106 : (DivisorBestState original mx_3 q 0 ans )) (PreH107 : (a_3 <> 0)) (PreH108 : (n_pre = (Zlength (original)))) (PreH109 : ((Zlength (copied)) = n_pre)) (PreH110 : ((Zlength (sorted)) = n_pre)) (PreH111 : (1 <= n_pre)) (PreH112 : (n_pre <= 2000)) (PreH113 : (1 <= all)) (PreH114 : (all <= 1000000000)) (PreH115 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH116 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH117 : (CopyMaxState original copied n_pre all )) (PreH118 : (LcmPrefixState copied n_pre all all )) (PreH119 : (Permutation copied sorted )) (PreH120 : (Permutation copied sorted )) (PreH121 : ((Zlength (sorted)) = n_pre)) (PreH122 : (all = mx_2)) (PreH123 : (i_2 >= n_pre)) (PreH124 : (a_3 <> 0)) (PreH125 : (n_pre = (Zlength (original)))) (PreH126 : ((Zlength (copied)) = n_pre)) (PreH127 : (1 <= n_pre)) (PreH128 : (n_pre <= 2000)) (PreH129 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH130 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH131 : (1 <= mx_2)) (PreH132 : (mx_2 <= 1000000000)) (PreH133 : (0 <= i_2)) (PreH134 : (i_2 <= n_pre)) (PreH135 : (1 <= all)) (PreH136 : (all <= (mx_2 + 1 ))) (PreH137 : (CopyMaxState original copied n_pre mx_2 )) (PreH138 : (LcmPrefixState copied i_2 mx_2 all )) (PreH139 : (finished_i >= n_pre)) (PreH140 : (a_2 <> 0)) (PreH141 : (n_pre = (Zlength (original)))) (PreH142 : (1 <= n_pre)) (PreH143 : (n_pre <= 2000)) (PreH144 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH145 : (0 <= finished_i)) (PreH146 : (finished_i <= n_pre)) (PreH147 : (0 <= mx)) (PreH148 : (mx <= 1000000000)) (PreH149 : (CopyMaxState original copied finished_i mx )) (PreH150 : (retval <> 0)) (PreH151 : (original = a)) (PreH152 : (n_pre = (Zlength (original)))) (PreH153 : (1 <= n_pre)) (PreH154 : (n_pre <= 2000)) (PreH155 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "present" ) )) # Int  |-> present)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((Znth i sorted 0) <= d) ”
).

Definition solver_partial_solve_wit_18_pure_split_goal_1 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : (l <= INT64_MAX)) (PreH2 : (all_4 <= INT64_MAX)) (PreH3 : (l >= INT64_MIN)) (PreH4 : (all_4 >= INT64_MIN)) (PreH5 : ((count + 1 ) <= INT_MAX)) (PreH6 : (present <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (ans_3 <= INT_MAX)) (PreH9 : (d <= INT_MAX)) (PreH10 : (z_2 <= INT_MAX)) (PreH11 : (q_3 <= INT_MAX)) (PreH12 : (mx_5 <= INT_MAX)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : ((count + 1 ) >= INT_MIN)) (PreH15 : (present >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (ans_3 >= INT_MIN)) (PreH18 : (d >= INT_MIN)) (PreH19 : (z_2 >= INT_MIN)) (PreH20 : (q_3 >= INT_MIN)) (PreH21 : (mx_5 >= INT_MIN)) (PreH22 : (n_pre >= INT_MIN)) (PreH23 : ((d % ( (Znth i sorted 0) ) ) = 0)) (PreH24 : ((Znth i sorted 0) <> d)) (PreH25 : (i < n_pre)) (PreH26 : (a_6 <> 0)) (PreH27 : (n_pre = (Zlength (original)))) (PreH28 : ((Zlength (copied)) = n_pre)) (PreH29 : ((Zlength (sorted)) = n_pre)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 2000)) (PreH32 : (1 <= mx_5)) (PreH33 : (mx_5 <= 1000000000)) (PreH34 : (all_4 = mx_5)) (PreH35 : (1 <= q_3)) (PreH36 : (q_3 <= 31623)) (PreH37 : ((q_3 * q_3 ) <= mx_5)) (PreH38 : ((mx_5 % ( q_3 ) ) = 0)) (PreH39 : (0 <= z_2)) (PreH40 : (z_2 < 2)) (PreH41 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH42 : (1 <= d)) (PreH43 : (d <= mx_5)) (PreH44 : (0 <= ans_3)) (PreH45 : (ans_3 <= n_pre)) (PreH46 : (0 <= i)) (PreH47 : (i <= n_pre)) (PreH48 : (0 <= present)) (PreH49 : (present <= 1)) (PreH50 : (0 <= count)) (PreH51 : (count <= i)) (PreH52 : (1 <= l)) (PreH53 : (l <= (d + 1 ))) (PreH54 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH55 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH56 : (CopyMaxState original copied n_pre mx_5 )) (PreH57 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH58 : (Permutation copied sorted )) (PreH59 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH60 : (DivisorScanState sorted d i present count l )) (PreH61 : (z < 2)) (PreH62 : (a_5 <> 0)) (PreH63 : (n_pre = (Zlength (original)))) (PreH64 : ((Zlength (copied)) = n_pre)) (PreH65 : ((Zlength (sorted)) = n_pre)) (PreH66 : (1 <= n_pre)) (PreH67 : (n_pre <= 2000)) (PreH68 : (1 <= mx_4)) (PreH69 : (mx_4 <= 1000000000)) (PreH70 : (all_3 = mx_4)) (PreH71 : (1 <= q_2)) (PreH72 : (q_2 <= 31623)) (PreH73 : ((q_2 * q_2 ) <= mx_4)) (PreH74 : ((mx_4 % ( q_2 ) ) = 0)) (PreH75 : (0 <= z)) (PreH76 : (z <= 2)) (PreH77 : (0 <= ans_2)) (PreH78 : (ans_2 <= n_pre)) (PreH79 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH80 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_4 )) (PreH82 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH85 : ((mx_3 % ( q ) ) = 0)) (PreH86 : ((q * q ) <= mx_3)) (PreH87 : (a_4 <> 0)) (PreH88 : (n_pre = (Zlength (original)))) (PreH89 : ((Zlength (copied)) = n_pre)) (PreH90 : ((Zlength (sorted)) = n_pre)) (PreH91 : (1 <= n_pre)) (PreH92 : (n_pre <= 2000)) (PreH93 : (1 <= mx_3)) (PreH94 : (mx_3 <= 1000000000)) (PreH95 : (all_2 = mx_3)) (PreH96 : (1 <= q)) (PreH97 : (q <= 31624)) (PreH98 : (0 <= ans)) (PreH99 : (ans <= n_pre)) (PreH100 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH101 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH102 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH103 : (CopyMaxState original copied n_pre mx_3 )) (PreH104 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH105 : (Permutation copied sorted )) (PreH106 : (DivisorBestState original mx_3 q 0 ans )) (PreH107 : (a_3 <> 0)) (PreH108 : (n_pre = (Zlength (original)))) (PreH109 : ((Zlength (copied)) = n_pre)) (PreH110 : ((Zlength (sorted)) = n_pre)) (PreH111 : (1 <= n_pre)) (PreH112 : (n_pre <= 2000)) (PreH113 : (1 <= all)) (PreH114 : (all <= 1000000000)) (PreH115 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH116 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH117 : (CopyMaxState original copied n_pre all )) (PreH118 : (LcmPrefixState copied n_pre all all )) (PreH119 : (Permutation copied sorted )) (PreH120 : (Permutation copied sorted )) (PreH121 : ((Zlength (sorted)) = n_pre)) (PreH122 : (all = mx_2)) (PreH123 : (i_2 >= n_pre)) (PreH124 : (a_3 <> 0)) (PreH125 : (n_pre = (Zlength (original)))) (PreH126 : ((Zlength (copied)) = n_pre)) (PreH127 : (1 <= n_pre)) (PreH128 : (n_pre <= 2000)) (PreH129 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH130 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH131 : (1 <= mx_2)) (PreH132 : (mx_2 <= 1000000000)) (PreH133 : (0 <= i_2)) (PreH134 : (i_2 <= n_pre)) (PreH135 : (1 <= all)) (PreH136 : (all <= (mx_2 + 1 ))) (PreH137 : (CopyMaxState original copied n_pre mx_2 )) (PreH138 : (LcmPrefixState copied i_2 mx_2 all )) (PreH139 : (finished_i >= n_pre)) (PreH140 : (a_2 <> 0)) (PreH141 : (n_pre = (Zlength (original)))) (PreH142 : (1 <= n_pre)) (PreH143 : (n_pre <= 2000)) (PreH144 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH145 : (0 <= finished_i)) (PreH146 : (finished_i <= n_pre)) (PreH147 : (0 <= mx)) (PreH148 : (mx <= 1000000000)) (PreH149 : (CopyMaxState original copied finished_i mx )) (PreH150 : (retval <> 0)) (PreH151 : (original = a)) (PreH152 : (n_pre = (Zlength (original)))) (PreH153 : (1 <= n_pre)) (PreH154 : (n_pre <= 2000)) (PreH155 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_6)
  **  ((( &( "mx" ) )) # Int  |-> mx_5)
  **  ((( &( "all" ) )) # Int64  |-> all_4)
  **  ((( &( "q" ) )) # Int  |-> q_3)
  **  ((( &( "z" ) )) # Int  |-> z_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "present" ) )) # Int  |-> present)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "l" ) )) # Int64  |-> l)
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ ((Znth i sorted 0) <= d) ”
.

Definition solver_partial_solve_wit_18_aux := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i_2: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (ans_2: Z) (z: Z) (q_2: Z) (all_3: Z) (mx_4: Z) (a_5: Z) (l: Z) (count: Z) (present: Z) (i: Z) (ans_3: Z) (d: Z) (z_2: Z) (q_3: Z) (all_4: Z) (mx_5: Z) (a_6: Z) (PreH1 : ((d % ( (Znth i sorted 0) ) ) = 0)) (PreH2 : ((Znth i sorted 0) <> d)) (PreH3 : (i < n_pre)) (PreH4 : (a_6 <> 0)) (PreH5 : (n_pre = (Zlength (original)))) (PreH6 : ((Zlength (copied)) = n_pre)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (1 <= mx_5)) (PreH11 : (mx_5 <= 1000000000)) (PreH12 : (all_4 = mx_5)) (PreH13 : (1 <= q_3)) (PreH14 : (q_3 <= 31623)) (PreH15 : ((q_3 * q_3 ) <= mx_5)) (PreH16 : ((mx_5 % ( q_3 ) ) = 0)) (PreH17 : (0 <= z_2)) (PreH18 : (z_2 < 2)) (PreH19 : (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0))) (PreH20 : (1 <= d)) (PreH21 : (d <= mx_5)) (PreH22 : (0 <= ans_3)) (PreH23 : (ans_3 <= n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= n_pre)) (PreH26 : (0 <= present)) (PreH27 : (present <= 1)) (PreH28 : (0 <= count)) (PreH29 : (count <= i)) (PreH30 : (1 <= l)) (PreH31 : (l <= (d + 1 ))) (PreH32 : forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000)))) (PreH33 : forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000)))) (PreH34 : (CopyMaxState original copied n_pre mx_5 )) (PreH35 : (LcmPrefixState copied n_pre mx_5 all_4 )) (PreH36 : (Permutation copied sorted )) (PreH37 : (DivisorBestState original mx_5 q_3 z_2 ans_3 )) (PreH38 : (DivisorScanState sorted d i present count l )) (PreH39 : (z < 2)) (PreH40 : (a_5 <> 0)) (PreH41 : (n_pre = (Zlength (original)))) (PreH42 : ((Zlength (copied)) = n_pre)) (PreH43 : ((Zlength (sorted)) = n_pre)) (PreH44 : (1 <= n_pre)) (PreH45 : (n_pre <= 2000)) (PreH46 : (1 <= mx_4)) (PreH47 : (mx_4 <= 1000000000)) (PreH48 : (all_3 = mx_4)) (PreH49 : (1 <= q_2)) (PreH50 : (q_2 <= 31623)) (PreH51 : ((q_2 * q_2 ) <= mx_4)) (PreH52 : ((mx_4 % ( q_2 ) ) = 0)) (PreH53 : (0 <= z)) (PreH54 : (z <= 2)) (PreH55 : (0 <= ans_2)) (PreH56 : (ans_2 <= n_pre)) (PreH57 : forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000)))) (PreH58 : forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000)))) (PreH59 : (CopyMaxState original copied n_pre mx_4 )) (PreH60 : (LcmPrefixState copied n_pre mx_4 all_3 )) (PreH61 : (Permutation copied sorted )) (PreH62 : (DivisorBestState original mx_4 q_2 z ans_2 )) (PreH63 : ((mx_3 % ( q ) ) = 0)) (PreH64 : ((q * q ) <= mx_3)) (PreH65 : (a_4 <> 0)) (PreH66 : (n_pre = (Zlength (original)))) (PreH67 : ((Zlength (copied)) = n_pre)) (PreH68 : ((Zlength (sorted)) = n_pre)) (PreH69 : (1 <= n_pre)) (PreH70 : (n_pre <= 2000)) (PreH71 : (1 <= mx_3)) (PreH72 : (mx_3 <= 1000000000)) (PreH73 : (all_2 = mx_3)) (PreH74 : (1 <= q)) (PreH75 : (q <= 31624)) (PreH76 : (0 <= ans)) (PreH77 : (ans <= n_pre)) (PreH78 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH79 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH80 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH81 : (CopyMaxState original copied n_pre mx_3 )) (PreH82 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH83 : (Permutation copied sorted )) (PreH84 : (DivisorBestState original mx_3 q 0 ans )) (PreH85 : (a_3 <> 0)) (PreH86 : (n_pre = (Zlength (original)))) (PreH87 : ((Zlength (copied)) = n_pre)) (PreH88 : ((Zlength (sorted)) = n_pre)) (PreH89 : (1 <= n_pre)) (PreH90 : (n_pre <= 2000)) (PreH91 : (1 <= all)) (PreH92 : (all <= 1000000000)) (PreH93 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH94 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH95 : (CopyMaxState original copied n_pre all )) (PreH96 : (LcmPrefixState copied n_pre all all )) (PreH97 : (Permutation copied sorted )) (PreH98 : (Permutation copied sorted )) (PreH99 : ((Zlength (sorted)) = n_pre)) (PreH100 : (all = mx_2)) (PreH101 : (i_2 >= n_pre)) (PreH102 : (a_3 <> 0)) (PreH103 : (n_pre = (Zlength (original)))) (PreH104 : ((Zlength (copied)) = n_pre)) (PreH105 : (1 <= n_pre)) (PreH106 : (n_pre <= 2000)) (PreH107 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH108 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH109 : (1 <= mx_2)) (PreH110 : (mx_2 <= 1000000000)) (PreH111 : (0 <= i_2)) (PreH112 : (i_2 <= n_pre)) (PreH113 : (1 <= all)) (PreH114 : (all <= (mx_2 + 1 ))) (PreH115 : (CopyMaxState original copied n_pre mx_2 )) (PreH116 : (LcmPrefixState copied i_2 mx_2 all )) (PreH117 : (finished_i >= n_pre)) (PreH118 : (a_2 <> 0)) (PreH119 : (n_pre = (Zlength (original)))) (PreH120 : (1 <= n_pre)) (PreH121 : (n_pre <= 2000)) (PreH122 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH123 : (0 <= finished_i)) (PreH124 : (finished_i <= n_pre)) (PreH125 : (0 <= mx)) (PreH126 : (mx <= 1000000000)) (PreH127 : (CopyMaxState original copied finished_i mx )) (PreH128 : (retval <> 0)) (PreH129 : (original = a)) (PreH130 : (n_pre = (Zlength (original)))) (PreH131 : (1 <= n_pre)) (PreH132 : (n_pre <= 2000)) (PreH133 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
|--
  “ (1 <= d) ” 
  &&  “ (d <= 1000000000) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ (1 <= (Znth i sorted 0)) ” 
  &&  “ ((Znth i sorted 0) <= d) ” 
  &&  “ ((d % ( (Znth i sorted 0) ) ) = 0) ” 
  &&  “ ((Znth i sorted 0) <> d) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a_6 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_5) ” 
  &&  “ (mx_5 <= 1000000000) ” 
  &&  “ (all_4 = mx_5) ” 
  &&  “ (1 <= q_3) ” 
  &&  “ (q_3 <= 31623) ” 
  &&  “ ((q_3 * q_3 ) <= mx_5) ” 
  &&  “ ((mx_5 % ( q_3 ) ) = 0) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (z_2 < 2) ” 
  &&  “ (d = (Znth z_2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) 0)) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= mx_5) ” 
  &&  “ (0 <= ans_3) ” 
  &&  “ (ans_3 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= present) ” 
  &&  “ (present <= 1) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (1 <= l) ” 
  &&  “ (l <= (d + 1 )) ” 
  &&  “ forall (k_11: Z) , (((0 <= k_11) /\ (k_11 < n_pre)) -> ((1 <= (Znth k_11 original 0)) /\ ((Znth k_11 original 0) <= 1000000000))) ” 
  &&  “ forall (k_12: Z) , (((0 <= k_12) /\ (k_12 < n_pre)) -> ((1 <= (Znth k_12 sorted 0)) /\ ((Znth k_12 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_5 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_5 all_4 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_5 q_3 z_2 ans_3 ) ” 
  &&  “ (DivisorScanState sorted d i present count l ) ” 
  &&  “ (z < 2) ” 
  &&  “ (a_5 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_4) ” 
  &&  “ (mx_4 <= 1000000000) ” 
  &&  “ (all_3 = mx_4) ” 
  &&  “ (1 <= q_2) ” 
  &&  “ (q_2 <= 31623) ” 
  &&  “ ((q_2 * q_2 ) <= mx_4) ” 
  &&  “ ((mx_4 % ( q_2 ) ) = 0) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= 2) ” 
  &&  “ (0 <= ans_2) ” 
  &&  “ (ans_2 <= n_pre) ” 
  &&  “ forall (k_9: Z) , (((0 <= k_9) /\ (k_9 < n_pre)) -> ((1 <= (Znth k_9 original 0)) /\ ((Znth k_9 original 0) <= 1000000000))) ” 
  &&  “ forall (k_10: Z) , (((0 <= k_10) /\ (k_10 < n_pre)) -> ((1 <= (Znth k_10 sorted 0)) /\ ((Znth k_10 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_4 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_4 all_3 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_4 q_2 z ans_2 ) ” 
  &&  “ ((mx_3 % ( q ) ) = 0) ” 
  &&  “ ((q * q ) <= mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i_2 >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i_2 mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full a_6 n_pre sorted )
  **  (IntArray.full input_pre n_pre original )
  **  (IntArray.full ( &( "ds" ) ) 2 (cons (q_3) ((cons ((mx_5 ÷ q_3 )) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_18 := solver_partial_solve_wit_18_pure -> solver_partial_solve_wit_18_aux.

Definition solver_partial_solve_wit_19 := 
forall (n_pre: Z) (input_pre: Z) (a: (@list Z)) (retval: Z) (original: (@list Z)) (mx: Z) (a_2: Z) (copied: (@list Z)) (finished_i: Z) (all: Z) (i: Z) (mx_2: Z) (a_3: Z) (sorted: (@list Z)) (ans: Z) (q: Z) (all_2: Z) (mx_3: Z) (a_4: Z) (PreH1 : (a_4 <> 0)) (PreH2 : (n_pre = (Zlength (original)))) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= all_2)) (PreH7 : (all_2 <= 1000000000)) (PreH8 : (all_2 = all_2)) (PreH9 : (0 <= ans)) (PreH10 : (ans <= n_pre)) (PreH11 : (Spec original ans )) (PreH12 : ((q * q ) > mx_3)) (PreH13 : (a_4 <> 0)) (PreH14 : (n_pre = (Zlength (original)))) (PreH15 : ((Zlength (copied)) = n_pre)) (PreH16 : ((Zlength (sorted)) = n_pre)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (1 <= mx_3)) (PreH20 : (mx_3 <= 1000000000)) (PreH21 : (all_2 = mx_3)) (PreH22 : (1 <= q)) (PreH23 : (q <= 31624)) (PreH24 : (0 <= ans)) (PreH25 : (ans <= n_pre)) (PreH26 : (((q - 1 ) * (q - 1 ) ) <= mx_3)) (PreH27 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000)))) (PreH28 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000)))) (PreH29 : (CopyMaxState original copied n_pre mx_3 )) (PreH30 : (LcmPrefixState copied n_pre mx_3 all_2 )) (PreH31 : (Permutation copied sorted )) (PreH32 : (DivisorBestState original mx_3 q 0 ans )) (PreH33 : (a_3 <> 0)) (PreH34 : (n_pre = (Zlength (original)))) (PreH35 : ((Zlength (copied)) = n_pre)) (PreH36 : ((Zlength (sorted)) = n_pre)) (PreH37 : (1 <= n_pre)) (PreH38 : (n_pre <= 2000)) (PreH39 : (1 <= all)) (PreH40 : (all <= 1000000000)) (PreH41 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000)))) (PreH42 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000)))) (PreH43 : (CopyMaxState original copied n_pre all )) (PreH44 : (LcmPrefixState copied n_pre all all )) (PreH45 : (Permutation copied sorted )) (PreH46 : (Permutation copied sorted )) (PreH47 : ((Zlength (sorted)) = n_pre)) (PreH48 : (all = mx_2)) (PreH49 : (i >= n_pre)) (PreH50 : (a_3 <> 0)) (PreH51 : (n_pre = (Zlength (original)))) (PreH52 : ((Zlength (copied)) = n_pre)) (PreH53 : (1 <= n_pre)) (PreH54 : (n_pre <= 2000)) (PreH55 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000)))) (PreH56 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000)))) (PreH57 : (1 <= mx_2)) (PreH58 : (mx_2 <= 1000000000)) (PreH59 : (0 <= i)) (PreH60 : (i <= n_pre)) (PreH61 : (1 <= all)) (PreH62 : (all <= (mx_2 + 1 ))) (PreH63 : (CopyMaxState original copied n_pre mx_2 )) (PreH64 : (LcmPrefixState copied i mx_2 all )) (PreH65 : (finished_i >= n_pre)) (PreH66 : (a_2 <> 0)) (PreH67 : (n_pre = (Zlength (original)))) (PreH68 : (1 <= n_pre)) (PreH69 : (n_pre <= 2000)) (PreH70 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000)))) (PreH71 : (0 <= finished_i)) (PreH72 : (finished_i <= n_pre)) (PreH73 : (0 <= mx)) (PreH74 : (mx <= 1000000000)) (PreH75 : (CopyMaxState original copied finished_i mx )) (PreH76 : (retval <> 0)) (PreH77 : (original = a)) (PreH78 : (n_pre = (Zlength (original)))) (PreH79 : (1 <= n_pre)) (PreH80 : (n_pre <= 2000)) (PreH81 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000)))) ,
  (IntArray.full input_pre n_pre original )
  **  (IntArray.full a_4 n_pre sorted )
|--
  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all_2) ” 
  &&  “ (all_2 <= 1000000000) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (Spec original ans ) ” 
  &&  “ ((q * q ) > mx_3) ” 
  &&  “ (a_4 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= mx_3) ” 
  &&  “ (mx_3 <= 1000000000) ” 
  &&  “ (all_2 = mx_3) ” 
  &&  “ (1 <= q) ” 
  &&  “ (q <= 31624) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ (((q - 1 ) * (q - 1 ) ) <= mx_3) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 original 0)) /\ ((Znth k_7 original 0) <= 1000000000))) ” 
  &&  “ forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((1 <= (Znth k_8 sorted 0)) /\ ((Znth k_8 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre mx_3 ) ” 
  &&  “ (LcmPrefixState copied n_pre mx_3 all_2 ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (DivisorBestState original mx_3 q 0 ans ) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= 1000000000) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 original 0)) /\ ((Znth k_5 original 0) <= 1000000000))) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 sorted 0)) /\ ((Znth k_6 sorted 0) <= 1000000000))) ” 
  &&  “ (CopyMaxState original copied n_pre all ) ” 
  &&  “ (LcmPrefixState copied n_pre all all ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ (Permutation copied sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (all = mx_2) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (a_3 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ ((Zlength (copied)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 original 0)) /\ ((Znth k_3 original 0) <= 1000000000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 copied 0)) /\ ((Znth k_4 copied 0) <= 1000000000))) ” 
  &&  “ (1 <= mx_2) ” 
  &&  “ (mx_2 <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= all) ” 
  &&  “ (all <= (mx_2 + 1 )) ” 
  &&  “ (CopyMaxState original copied n_pre mx_2 ) ” 
  &&  “ (LcmPrefixState copied i mx_2 all ) ” 
  &&  “ (finished_i >= n_pre) ” 
  &&  “ (a_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 original 0)) /\ ((Znth k_2 original 0) <= 1000000000))) ” 
  &&  “ (0 <= finished_i) ” 
  &&  “ (finished_i <= n_pre) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 1000000000) ” 
  &&  “ (CopyMaxState original copied finished_i mx ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (original = a) ” 
  &&  “ (n_pre = (Zlength (original))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k original 0)) /\ ((Znth k original 0) <= 1000000000))) ”
  &&  (IntArray.full a_4 (Zlength (a)) sorted )
  **  (IntArray.full input_pre n_pre original )
.

Definition solver_which_implies_wit_1 := 
(
forall (n_pre: Z) (copied: (@list Z)) (finished_i: Z) (a: Z) (PreH1 : (finished_i = n_pre)) (PreH2 : ((Zlength (copied)) = finished_i)) ,
  (IntArray.seg a 0 finished_i copied )
|--
  (IntArray.full a n_pre copied )
) \/
(
forall (n_pre: Z) (copied: (@list Z)) (finished_i: Z) (a: Z) (PreH1 : (finished_i = n_pre)) (PreH2 : ((Zlength (copied)) = finished_i)) ,
  (IntArray.seg a 0 finished_i copied )
|--
  (IntArray.full a n_pre copied )
).

Definition solver_which_implies_wit_1_split_goal_spatial := 
forall (n_pre: Z) (copied: (@list Z)) (finished_i: Z) (a: Z) (PreH1 : (finished_i = n_pre)) (PreH2 : ((Zlength (copied)) = finished_i)) ,
  (IntArray.seg a 0 finished_i copied )
|--
  (IntArray.full a n_pre copied )
.

Module Type VC_Correct.


Axiom proof_of_gcdll_safety_wit_1 : gcdll_safety_wit_1.
Axiom proof_of_gcdll_entail_wit_1 : gcdll_entail_wit_1.
Axiom proof_of_gcdll_entail_wit_2 : gcdll_entail_wit_2.
Axiom proof_of_gcdll_return_wit_1 : gcdll_return_wit_1.
Axiom proof_of_lcm_cap_safety_wit_1 : lcm_cap_safety_wit_1.
Axiom proof_of_lcm_cap_safety_wit_2 : lcm_cap_safety_wit_2.
Axiom proof_of_lcm_cap_safety_wit_3 : lcm_cap_safety_wit_3.
Axiom proof_of_lcm_cap_safety_wit_4 : lcm_cap_safety_wit_4.
Axiom proof_of_lcm_cap_safety_wit_5 : lcm_cap_safety_wit_5.
Axiom proof_of_lcm_cap_safety_wit_6 : lcm_cap_safety_wit_6.
Axiom proof_of_lcm_cap_safety_wit_7 : lcm_cap_safety_wit_7.
Axiom proof_of_lcm_cap_safety_wit_8 : lcm_cap_safety_wit_8.
Axiom proof_of_lcm_cap_entail_wit_1 : lcm_cap_entail_wit_1.
Axiom proof_of_lcm_cap_return_wit_1 : lcm_cap_return_wit_1.
Axiom proof_of_lcm_cap_return_wit_2 : lcm_cap_return_wit_2.
Axiom proof_of_lcm_cap_return_wit_3 : lcm_cap_return_wit_3.
Axiom proof_of_lcm_cap_partial_solve_wit_1_pure : lcm_cap_partial_solve_wit_1_pure.
Axiom proof_of_lcm_cap_partial_solve_wit_1 : lcm_cap_partial_solve_wit_1.
Axiom proof_of_cmp_int_safety_wit_1 : cmp_int_safety_wit_1.
Axiom proof_of_cmp_int_safety_wit_2 : cmp_int_safety_wit_2.
Axiom proof_of_cmp_int_safety_wit_3 : cmp_int_safety_wit_3.
Axiom proof_of_cmp_int_safety_wit_4 : cmp_int_safety_wit_4.
Axiom proof_of_cmp_int_return_wit_1 : cmp_int_return_wit_1.
Axiom proof_of_cmp_int_return_wit_2 : cmp_int_return_wit_2.
Axiom proof_of_cmp_int_return_wit_3 : cmp_int_return_wit_3.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3.
Axiom proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4.
Axiom proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Axiom proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Axiom proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Axiom proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8_pure : solver_partial_solve_wit_8_pure.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10_pure : solver_partial_solve_wit_10_pure.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16_pure : solver_partial_solve_wit_16_pure.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18_pure : solver_partial_solve_wit_18_pure.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.

End VC_Correct.
