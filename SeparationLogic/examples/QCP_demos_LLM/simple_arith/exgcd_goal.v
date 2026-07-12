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

(*----- Function exgcd -----*)

Definition exgcd_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition exgcd_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition exgcd_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_6 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_7 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition exgcd_safety_wit_8 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_9 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_10 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_11 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) ” 
  &&  “ (b_pre <> 0) ”
.

Definition exgcd_safety_wit_12 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) )) ”
.

Definition exgcd_safety_wit_13 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_callee_v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_callee_v )) ”
.

Definition exgcd_safety_wit_14 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) ” 
  &&  “ (b_pre <> 0) ”
.

Definition exgcd_safety_wit_15 := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) )) ”
).

Definition exgcd_safety_wit_15_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) <= INT_MAX) ”
.

Definition exgcd_safety_wit_15_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) )) ”
.

Definition exgcd_safety_wit_16 := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_callee_v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_callee_v )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_callee_v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_callee_v )) ”
).

Definition exgcd_safety_wit_16_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_callee_v ) <= INT_MAX) ”
.

Definition exgcd_safety_wit_16_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_callee_v )) ”
.

Definition exgcd_safety_wit_17 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) ” 
  &&  “ (b_pre <> 0) ”
.

Definition exgcd_safety_wit_18 := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) )) ”
).

Definition exgcd_safety_wit_18_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) <= INT_MAX) ”
.

Definition exgcd_safety_wit_18_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) )) ”
.

Definition exgcd_safety_wit_19 := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_callee_v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_callee_v )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_callee_v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_callee_v )) ”
).

Definition exgcd_safety_wit_19_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_callee_v ) <= INT_MAX) ”
.

Definition exgcd_safety_wit_19_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_callee_v )) ”
.

Definition exgcd_safety_wit_20 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) ” 
  &&  “ (b_pre <> 0) ”
.

Definition exgcd_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))
  **  ((x_pre) # Int  |-> y_callee_v)
|--
  EX (y_pre_v_2: Z)  (x_pre_v_2: Z) ,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ ((a_pre % ( b_pre ) ) = 0) ” 
  &&  “ (x_pre_v_2 = 0) ” 
  &&  “ ((Zabs (y_pre_v_2)) <= 1) ”
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2)
) \/
(
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))) <= 1) ” 
  &&  “ (((a_pre * 0 ) + (b_pre * (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition exgcd_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  ((Zabs ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))) <= 1)
.

Definition exgcd_return_wit_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  (((a_pre * 0 ) + (b_pre * (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) ) ) = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_1_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))
  **  ((x_pre) # Int  |-> y_callee_v)
|--
  EX (y_pre_v_3: Z)  (x_pre_v_3: Z) ,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ ((a_pre % ( b_pre ) ) <> 0) ” 
  &&  “ ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ” 
  &&  “ ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3)
) \/
(
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ” 
  &&  “ ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ” 
  &&  “ (((a_pre * y_callee_v ) + (b_pre * (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition exgcd_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((Zabs ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) ))
.

Definition exgcd_return_wit_2_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) ))
.

Definition exgcd_return_wit_2_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  (((a_pre * y_callee_v ) + (b_pre * (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) ) ) = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_2_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_callee_v = 0)) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_3 := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int  |-> (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))
  **  ((x_pre) # Int  |-> y_callee_v)
|--
  EX (y_pre_v_3: Z)  (x_pre_v_3: Z) ,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ ((a_pre % ( b_pre ) ) <> 0) ” 
  &&  “ ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ” 
  &&  “ ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3)
) \/
(
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ” 
  &&  “ ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ” 
  &&  “ (((a_pre * y_callee_v ) + (b_pre * (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition exgcd_return_wit_3_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((Zabs ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) ))
.

Definition exgcd_return_wit_3_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) ))
.

Definition exgcd_return_wit_3_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  (((a_pre * y_callee_v ) + (b_pre * (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) ) ) = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_3_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_4 := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  EX (y_pre_v: Z)  (x_pre_v: Z) ,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (b_pre = 0) ” 
  &&  “ ((Zabs (x_pre_v)) <= 1) ” 
  &&  “ (y_pre_v = 0) ”
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v)
) \/
(
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs ((-1))) <= 1) ” 
  &&  “ (((a_pre * (-1) ) + (b_pre * 0 ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition exgcd_return_wit_4_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((Zabs ((-1))) <= 1)
.

Definition exgcd_return_wit_4_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  (((a_pre * (-1) ) + (b_pre * 0 ) ) = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_4_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_5 := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  EX (y_pre_v: Z)  (x_pre_v: Z) ,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (b_pre = 0) ” 
  &&  “ ((Zabs (x_pre_v)) <= 1) ” 
  &&  “ (y_pre_v = 0) ”
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v)
) \/
(
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs (0)) <= 1) ” 
  &&  “ (((a_pre * 0 ) + (b_pre * 0 ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition exgcd_return_wit_5_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  ((Zabs (0)) <= 1)
.

Definition exgcd_return_wit_5_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  (((a_pre * 0 ) + (b_pre * 0 ) ) = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_5_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_6 := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre <> 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  EX (y_pre_v: Z)  (x_pre_v: Z) ,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (b_pre = 0) ” 
  &&  “ ((Zabs (x_pre_v)) <= 1) ” 
  &&  “ (y_pre_v = 0) ”
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v)
) \/
(
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre <> 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs (1)) <= 1) ” 
  &&  “ (((a_pre * 1 ) + (b_pre * 0 ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition exgcd_return_wit_6_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre <> 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  ((Zabs (1)) <= 1)
.

Definition exgcd_return_wit_6_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre <> 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  (((a_pre * 1 ) + (b_pre * 0 ) ) = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_6_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre <> 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ”
.

Definition exgcd_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (a_pre < 0) ” 
  &&  “ (b_pre = 0) ” 
  &&  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
.

Definition exgcd_partial_solve_wit_1 := exgcd_partial_solve_wit_1_pure -> exgcd_partial_solve_wit_1_aux.

Definition exgcd_partial_solve_wit_2_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ”
.

Definition exgcd_partial_solve_wit_2_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (a_pre = 0) ” 
  &&  “ (a_pre >= 0) ” 
  &&  “ (b_pre = 0) ” 
  &&  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
.

Definition exgcd_partial_solve_wit_2 := exgcd_partial_solve_wit_2_pure -> exgcd_partial_solve_wit_2_aux.

Definition exgcd_partial_solve_wit_3_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ”
.

Definition exgcd_partial_solve_wit_3_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (a_pre >= 0) ” 
  &&  “ (b_pre = 0) ” 
  &&  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
.

Definition exgcd_partial_solve_wit_3 := exgcd_partial_solve_wit_3_pure -> exgcd_partial_solve_wit_3_aux.

Definition exgcd_partial_solve_wit_4_pure := 
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (a_pre % ( b_pre ) )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= INT_MIN)) (PreH2 : (b_pre >= INT_MIN)) (PreH3 : (b_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (INT_MIN < (a_pre % ( b_pre ) )) ” 
  &&  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ”
).

Definition exgcd_partial_solve_wit_4_pure_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= INT_MIN)) (PreH2 : (b_pre >= INT_MIN)) (PreH3 : (b_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (INT_MIN < (a_pre % ( b_pre ) )) ”
.

Definition exgcd_partial_solve_wit_4_pure_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= INT_MIN)) (PreH2 : (b_pre >= INT_MIN)) (PreH3 : (b_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ”
.

Definition exgcd_partial_solve_wit_4_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (a_pre % ( b_pre ) )) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ”
  &&  ((y_pre) # Int  |->_)
  **  ((x_pre) # Int  |->_)
.

Definition exgcd_partial_solve_wit_4 := exgcd_partial_solve_wit_4_pure -> exgcd_partial_solve_wit_4_aux.

Definition exgcd_derive_Inter_by_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  (“ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_))
  **
  (((EX y_callee_v x_callee_v retval_2,
  “ (retval_2 = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (((a_pre * x_callee_v ) + (b_pre * y_callee_v ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (b_pre = 0) ” 
  &&  “ ((Zabs (x_callee_v)) <= 1) ” 
  &&  “ (y_callee_v = 0) ”
  &&  ((x_pre) # Int  |-> x_callee_v)
  **  ((y_pre) # Int  |-> y_callee_v))
  ||
  (EX y_callee_v_2 x_callee_v_2 retval_2,
  “ (retval_2 = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (((a_pre * x_callee_v_2 ) + (b_pre * y_callee_v_2 ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ ((a_pre % ( b_pre ) ) = 0) ” 
  &&  “ (x_callee_v_2 = 0) ” 
  &&  “ ((Zabs (y_callee_v_2)) <= 1) ”
  &&  ((x_pre) # Int  |-> x_callee_v_2)
  **  ((y_pre) # Int  |-> y_callee_v_2))
  ||
  (EX y_callee_v_3 x_callee_v_3 retval_2,
  “ (retval_2 = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (((a_pre * x_callee_v_3 ) + (b_pre * y_callee_v_3 ) ) = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ ((a_pre % ( b_pre ) ) <> 0) ” 
  &&  “ ((Zabs (x_callee_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ” 
  &&  “ ((Zabs (y_callee_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  ((x_pre) # Int  |-> x_callee_v_3)
  **  ((y_pre) # Int  |-> y_callee_v_3)))
  -*
  (EX y_pre_v x_pre_v retval,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” 
  &&  “ (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v)))
.

Module Type VC_Correct.


Axiom proof_of_exgcd_safety_wit_1 : exgcd_safety_wit_1.
Axiom proof_of_exgcd_safety_wit_2 : exgcd_safety_wit_2.
Axiom proof_of_exgcd_safety_wit_3 : exgcd_safety_wit_3.
Axiom proof_of_exgcd_safety_wit_4 : exgcd_safety_wit_4.
Axiom proof_of_exgcd_safety_wit_5 : exgcd_safety_wit_5.
Axiom proof_of_exgcd_safety_wit_6 : exgcd_safety_wit_6.
Axiom proof_of_exgcd_safety_wit_7 : exgcd_safety_wit_7.
Axiom proof_of_exgcd_safety_wit_8 : exgcd_safety_wit_8.
Axiom proof_of_exgcd_safety_wit_9 : exgcd_safety_wit_9.
Axiom proof_of_exgcd_safety_wit_10 : exgcd_safety_wit_10.
Axiom proof_of_exgcd_safety_wit_11 : exgcd_safety_wit_11.
Axiom proof_of_exgcd_safety_wit_12 : exgcd_safety_wit_12.
Axiom proof_of_exgcd_safety_wit_13 : exgcd_safety_wit_13.
Axiom proof_of_exgcd_safety_wit_14 : exgcd_safety_wit_14.
Axiom proof_of_exgcd_safety_wit_15 : exgcd_safety_wit_15.
Axiom proof_of_exgcd_safety_wit_16 : exgcd_safety_wit_16.
Axiom proof_of_exgcd_safety_wit_17 : exgcd_safety_wit_17.
Axiom proof_of_exgcd_safety_wit_18 : exgcd_safety_wit_18.
Axiom proof_of_exgcd_safety_wit_19 : exgcd_safety_wit_19.
Axiom proof_of_exgcd_safety_wit_20 : exgcd_safety_wit_20.
Axiom proof_of_exgcd_return_wit_1 : exgcd_return_wit_1.
Axiom proof_of_exgcd_return_wit_2 : exgcd_return_wit_2.
Axiom proof_of_exgcd_return_wit_3 : exgcd_return_wit_3.
Axiom proof_of_exgcd_return_wit_4 : exgcd_return_wit_4.
Axiom proof_of_exgcd_return_wit_5 : exgcd_return_wit_5.
Axiom proof_of_exgcd_return_wit_6 : exgcd_return_wit_6.
Axiom proof_of_exgcd_partial_solve_wit_1_pure : exgcd_partial_solve_wit_1_pure.
Axiom proof_of_exgcd_partial_solve_wit_1 : exgcd_partial_solve_wit_1.
Axiom proof_of_exgcd_partial_solve_wit_2_pure : exgcd_partial_solve_wit_2_pure.
Axiom proof_of_exgcd_partial_solve_wit_2 : exgcd_partial_solve_wit_2.
Axiom proof_of_exgcd_partial_solve_wit_3_pure : exgcd_partial_solve_wit_3_pure.
Axiom proof_of_exgcd_partial_solve_wit_3 : exgcd_partial_solve_wit_3.
Axiom proof_of_exgcd_partial_solve_wit_4_pure : exgcd_partial_solve_wit_4_pure.
Axiom proof_of_exgcd_partial_solve_wit_4 : exgcd_partial_solve_wit_4.
Axiom proof_of_exgcd_derive_Inter_by_Proof : exgcd_derive_Inter_by_Proof.

End VC_Correct.
