From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Local Open Scope sac.

(*----- Function exgcd -----*)

Definition exgcd_safety_wit_1 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_2 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (b_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_3 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre < 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition exgcd_safety_wit_4 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre < 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition exgcd_safety_wit_5 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre >= 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_6 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_7 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition exgcd_safety_wit_8 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre < 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_9 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_10 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition exgcd_safety_wit_11 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)),
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) ”
  &&  “ (b_pre <> 0) ”
.

Definition exgcd_safety_wit_12 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_v)) <= 1)) (PreH5 : (y_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((x_v - ((a_pre ÷ b_pre ) * y_v ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x_v - ((a_pre ÷ b_pre ) * y_v ) )) ”
.

Definition exgcd_safety_wit_13 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_v)) <= 1)) (PreH5 : (y_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_v )) ”
.

Definition exgcd_safety_wit_14 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_v)) <= 1)) (PreH5 : (y_v = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) ”
  &&  “ (b_pre <> 0) ”
.

Definition exgcd_safety_wit_15 :=
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v = 0)) (PreH6 : ((Zabs (y_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((x_v - ((a_pre ÷ b_pre ) * y_v ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x_v - ((a_pre ÷ b_pre ) * y_v ) )) ”
) \/
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v = 0)) (PreH6 : ((Zabs (y_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((x_v - ((a_pre ÷ b_pre ) * y_v ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x_v - ((a_pre ÷ b_pre ) * y_v ) )) ”
).

Definition exgcd_safety_wit_15_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v = 0)) (PreH6 : ((Zabs (y_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((x_v - ((a_pre ÷ b_pre ) * y_v ) ) <= INT_MAX) ”
.

Definition exgcd_safety_wit_15_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v = 0)) (PreH6 : ((Zabs (y_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((INT_MIN) <= (x_v - ((a_pre ÷ b_pre ) * y_v ) )) ”
.

Definition exgcd_safety_wit_16 :=
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v = 0)) (PreH6 : ((Zabs (y_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_v )) ”
) \/
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v = 0)) (PreH6 : ((Zabs (y_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_v )) ”
).

Definition exgcd_safety_wit_16_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v = 0)) (PreH6 : ((Zabs (y_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_v ) <= INT_MAX) ”
.

Definition exgcd_safety_wit_16_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v = 0)) (PreH6 : ((Zabs (y_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_v )) ”
.

Definition exgcd_safety_wit_17 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v = 0)) (PreH6 : ((Zabs (y_v)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) ”
  &&  “ (b_pre <> 0) ”
.

Definition exgcd_safety_wit_18 :=
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((x_v - ((a_pre ÷ b_pre ) * y_v ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x_v - ((a_pre ÷ b_pre ) * y_v ) )) ”
) \/
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((x_v - ((a_pre ÷ b_pre ) * y_v ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x_v - ((a_pre ÷ b_pre ) * y_v ) )) ”
).

Definition exgcd_safety_wit_18_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((x_v - ((a_pre ÷ b_pre ) * y_v ) ) <= INT_MAX) ”
.

Definition exgcd_safety_wit_18_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((INT_MIN) <= (x_v - ((a_pre ÷ b_pre ) * y_v ) )) ”
.

Definition exgcd_safety_wit_19 :=
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_v )) ”
) \/
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_v )) ”
).

Definition exgcd_safety_wit_19_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (((a_pre ÷ b_pre ) * y_v ) <= INT_MAX) ”
.

Definition exgcd_safety_wit_19_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_v )) ”
.

Definition exgcd_safety_wit_20 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v: Z) (x_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v ) + ((a_pre % ( b_pre ) ) * y_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> x_v)
  **  ((x_pre) # Int  |-> y_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) ”
  &&  “ (b_pre <> 0) ”
.

Definition exgcd_return_wit_1 :=
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_v_4)) <= 1)) (PreH5 : (y_v_4 = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> (x_v_4 - ((a_pre ÷ b_pre ) * y_v_4 ) ))
  **  ((x_pre) # Int  |-> y_v_4)
|--
  EX (y_v_2: Z) (x_v_2: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v_2 ) + (b_pre * y_v_2 ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre <> 0) ”
  &&  “ ((a_pre % ( b_pre ) ) = 0) ”
  &&  “ (x_v_2 = 0) ”
  &&  “ ((Zabs (y_v_2)) <= 1) ”
  &&  ((x_pre) # Int  |-> x_v_2)
  **  ((y_pre) # Int  |-> y_v_2)
) \/
(
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_v_4)) <= 1)) (PreH5 : (y_v_4 = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)),
  TT && emp 
|--
  “ ((Zabs ((x_v_4 - ((a_pre ÷ b_pre ) * 0 ) ))) <= 1) ”
  &&  “ (((a_pre * 0 ) + (b_pre * (x_v_4 - ((a_pre ÷ b_pre ) * 0 ) ) ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition exgcd_return_wit_1_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_v_4)) <= 1)) (PreH5 : (y_v_4 = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)),
  ((Zabs ((x_v_4 - ((a_pre ÷ b_pre ) * 0 ) ))) <= 1)
.

Definition exgcd_return_wit_1_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_v_4)) <= 1)) (PreH5 : (y_v_4 = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)),
  (((a_pre * 0 ) + (b_pre * (x_v_4 - ((a_pre ÷ b_pre ) * 0 ) ) ) ) = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_1_split_goal_3 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) = 0)) (PreH4 : ((Zabs (x_v_4)) <= 1)) (PreH5 : (y_v_4 = 0)) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)),
  (retval = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_2 :=
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v_4 = 0)) (PreH6 : ((Zabs (y_v_4)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> (x_v_4 - ((a_pre ÷ b_pre ) * y_v_4 ) ))
  **  ((x_pre) # Int  |-> y_v_4)
|--
  EX (y_v_3: Z) (x_v_3: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v_3 ) + (b_pre * y_v_3 ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre <> 0) ”
  &&  “ ((a_pre % ( b_pre ) ) <> 0) ”
  &&  “ ((Zabs (x_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  “ ((Zabs (y_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  ((x_pre) # Int  |-> x_v_3)
  **  ((y_pre) # Int  |-> y_v_3)
) \/
(
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v_4 = 0)) (PreH6 : ((Zabs (y_v_4)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  TT && emp 
|--
  “ ((Zabs ((0 - ((a_pre ÷ b_pre ) * y_v_4 ) ))) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  “ ((Zabs (y_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  “ (((a_pre * y_v_4 ) + (b_pre * (0 - ((a_pre ÷ b_pre ) * y_v_4 ) ) ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition exgcd_return_wit_2_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v_4 = 0)) (PreH6 : ((Zabs (y_v_4)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((Zabs ((0 - ((a_pre ÷ b_pre ) * y_v_4 ) ))) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) ))
.

Definition exgcd_return_wit_2_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v_4 = 0)) (PreH6 : ((Zabs (y_v_4)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((Zabs (y_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) ))
.

Definition exgcd_return_wit_2_split_goal_3 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v_4 = 0)) (PreH6 : ((Zabs (y_v_4)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  (((a_pre * y_v_4 ) + (b_pre * (0 - ((a_pre ÷ b_pre ) * y_v_4 ) ) ) ) = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_2_split_goal_4 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0)) (PreH5 : (x_v_4 = 0)) (PreH6 : ((Zabs (y_v_4)) <= 1)) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  (retval = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_3 :=
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v_4)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((y_pre) # Int  |-> (x_v_4 - ((a_pre ÷ b_pre ) * y_v_4 ) ))
  **  ((x_pre) # Int  |-> y_v_4)
|--
  EX (y_v_3: Z) (x_v_3: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v_3 ) + (b_pre * y_v_3 ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre <> 0) ”
  &&  “ ((a_pre % ( b_pre ) ) <> 0) ”
  &&  “ ((Zabs (x_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  “ ((Zabs (y_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  ((x_pre) # Int  |-> x_v_3)
  **  ((y_pre) # Int  |-> y_v_3)
) \/
(
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v_4)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  TT && emp 
|--
  “ ((Zabs ((x_v_4 - ((a_pre ÷ b_pre ) * y_v_4 ) ))) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  “ ((Zabs (y_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  “ (((a_pre * y_v_4 ) + (b_pre * (x_v_4 - ((a_pre ÷ b_pre ) * y_v_4 ) ) ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition exgcd_return_wit_3_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v_4)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((Zabs ((x_v_4 - ((a_pre ÷ b_pre ) * y_v_4 ) ))) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) ))
.

Definition exgcd_return_wit_3_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v_4)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  ((Zabs (y_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) ))
.

Definition exgcd_return_wit_3_split_goal_3 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v_4)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  (((a_pre * y_v_4 ) + (b_pre * (x_v_4 - ((a_pre ÷ b_pre ) * y_v_4 ) ) ) ) = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_3_split_goal_4 :=
forall (a_pre: Z) (b_pre: Z) (y_v_4: Z) (x_v_4: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (((b_pre * x_v_4 ) + ((a_pre % ( b_pre ) ) * y_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH3 : ((a_pre % ( b_pre ) ) <> 0)) (PreH4 : ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0)) (PreH5 : ((Zabs (x_v_4)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH6 : ((Zabs (y_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) ))) (PreH7 : (b_pre <> 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)),
  (retval = (Zgcd (a_pre) (b_pre)))
.

Definition exgcd_return_wit_4 :=
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  EX (y_v: Z) (x_v: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v ) + (b_pre * y_v ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre = 0) ”
  &&  “ ((Zabs (x_v)) <= 1) ”
  &&  “ (y_v = 0) ”
  &&  ((x_pre) # Int  |-> x_v)
  **  ((y_pre) # Int  |-> y_v)
) \/
(
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  TT && emp 
|--
  “ ((Zabs ((-1))) <= 1) ”
  &&  “ (((a_pre * (-1) ) + (0 * 0 ) ) = (Zgcd (a_pre) (0))) ”
  &&  “ (retval = (Zgcd (a_pre) (0))) ”
  &&  emp
).

Definition exgcd_return_wit_4_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((Zabs ((-1))) <= 1)
.

Definition exgcd_return_wit_4_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  (((a_pre * (-1) ) + (0 * 0 ) ) = (Zgcd (a_pre) (0)))
.

Definition exgcd_return_wit_4_split_goal_3 :=
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  (retval = (Zgcd (a_pre) (0)))
.

Definition exgcd_return_wit_5 :=
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)),
  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  EX (y_v: Z) (x_v: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v ) + (b_pre * y_v ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre = 0) ”
  &&  “ ((Zabs (x_v)) <= 1) ”
  &&  “ (y_v = 0) ”
  &&  ((x_pre) # Int  |-> x_v)
  **  ((y_pre) # Int  |-> y_v)
) \/
(
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)),
  TT && emp 
|--
  “ ((Zabs (0)) <= 1) ”
  &&  “ (((0 * 0 ) + (0 * 0 ) ) = (Zgcd (0) (0))) ”
  &&  “ (retval = (Zgcd (0) (0))) ”
  &&  emp
).

Definition exgcd_return_wit_5_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)),
  ((Zabs (0)) <= 1)
.

Definition exgcd_return_wit_5_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)),
  (((0 * 0 ) + (0 * 0 ) ) = (Zgcd (0) (0)))
.

Definition exgcd_return_wit_5_split_goal_3 :=
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)),
  (retval = (Zgcd (0) (0)))
.

Definition exgcd_return_wit_6 :=
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre <> 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)),
  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  EX (y_v: Z) (x_v: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v ) + (b_pre * y_v ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre = 0) ”
  &&  “ ((Zabs (x_v)) <= 1) ”
  &&  “ (y_v = 0) ”
  &&  ((x_pre) # Int  |-> x_v)
  **  ((y_pre) # Int  |-> y_v)
) \/
(
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre <> 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)),
  TT && emp 
|--
  “ ((Zabs (1)) <= 1) ”
  &&  “ (((a_pre * 1 ) + (0 * 0 ) ) = (Zgcd (a_pre) (0))) ”
  &&  “ (retval = (Zgcd (a_pre) (0))) ”
  &&  emp
).

Definition exgcd_return_wit_6_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre <> 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)),
  ((Zabs (1)) <= 1)
.

Definition exgcd_return_wit_6_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre <> 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)),
  (((a_pre * 1 ) + (0 * 0 ) ) = (Zgcd (a_pre) (0)))
.

Definition exgcd_return_wit_6_split_goal_3 :=
forall (a_pre: Z) (b_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre <> 0)) (PreH3 : (a_pre >= 0)) (PreH4 : (b_pre = 0)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)),
  (retval = (Zgcd (a_pre) (0)))
.

Definition exgcd_partial_solve_wit_1_pure :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre < 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  “ (INT_MIN < a_pre) ”
  &&  “ (a_pre <= INT_MAX) ”
.

Definition exgcd_partial_solve_wit_1_aux :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre < 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)),
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
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  “ (INT_MIN < a_pre) ”
  &&  “ (a_pre <= INT_MAX) ”
.

Definition exgcd_partial_solve_wit_2_aux :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
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
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  “ (INT_MIN < a_pre) ”
  &&  “ (a_pre <= INT_MAX) ”
.

Definition exgcd_partial_solve_wit_3_aux :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (a_pre >= 0)) (PreH3 : (b_pre = 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
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
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)),
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (INT_MIN < b_pre) ”
  &&  “ (b_pre <= INT_MAX) ”
  &&  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ”
  &&  “ (INT_MIN < (a_pre % ( b_pre ) )) ”
) \/
(
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (b_pre >= INT_MIN)) (PreH2 : (a_pre >= INT_MIN)) (PreH3 : (b_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (INT_MIN < (a_pre % ( b_pre ) )) ”
  &&  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ”
).

Definition exgcd_partial_solve_wit_4_pure_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (b_pre >= INT_MIN)) (PreH2 : (a_pre >= INT_MIN)) (PreH3 : (b_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ (INT_MIN < (a_pre % ( b_pre ) )) ”
.

Definition exgcd_partial_solve_wit_4_pure_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (b_pre >= INT_MIN)) (PreH2 : (a_pre >= INT_MIN)) (PreH3 : (b_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)),
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ”
.

Definition exgcd_partial_solve_wit_4_aux :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)),
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

(* Shallow FunAssertion specs for exgcd. *)
Definition exgcd_sig : FuncSig := ([i32; i32;  * i32;  * i32], i32)%ctype.

Definition exgcd_Proof : Spec exgcd_sig :=
  fun F =>
HoareFun ([i32; i32;  * i32;  * i32], i32)%ctype
  (fun '(a_pre, (b_pre, (x_pre, y_pre))) =>
  (“ (INT_MIN < a_pre) ”
  &&  “ (a_pre <= INT_MAX) ”
  &&  “ (INT_MIN < b_pre) ”
  &&  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)))
  (fun '(a_pre, (b_pre, (x_pre, y_pre))) retval =>
(orp
  (EX (y_v: Z) (x_v: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v ) + (b_pre * y_v ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre = 0) ”
  &&  “ ((Zabs (x_v)) <= 1) ”
  &&  “ (y_v = 0) ”
  &&  ((x_pre) # Int  |-> x_v)
  **  ((y_pre) # Int  |-> y_v))
(orp
  (EX (y_v_2: Z) (x_v_2: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v_2 ) + (b_pre * y_v_2 ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre <> 0) ”
  &&  “ ((a_pre % ( b_pre ) ) = 0) ”
  &&  “ (x_v_2 = 0) ”
  &&  “ ((Zabs (y_v_2)) <= 1) ”
  &&  ((x_pre) # Int  |-> x_v_2)
  **  ((y_pre) # Int  |-> y_v_2))
  (EX (y_v_3: Z) (x_v_3: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v_3 ) + (b_pre * y_v_3 ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre <> 0) ”
  &&  “ ((a_pre % ( b_pre ) ) <> 0) ”
  &&  “ ((Zabs (x_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  “ ((Zabs (y_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  ((x_pre) # Int  |-> x_v_3)
  **  ((y_pre) # Int  |-> y_v_3)))))
  F.

Definition exgcd_Inter : Spec exgcd_sig :=
  fun F =>
HoareFun ([i32; i32;  * i32;  * i32], i32)%ctype
  (fun '(a_pre, (b_pre, (x_pre, y_pre))) =>
  (“ (INT_MIN < a_pre) ”
  &&  “ (a_pre <= INT_MAX) ”
  &&  “ (INT_MIN < b_pre) ”
  &&  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)))
  (fun '(a_pre, (b_pre, (x_pre, y_pre))) retval =>
  (EX (y_v: Z) (x_v: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v ) + (b_pre * y_v ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  ((x_pre) # Int  |-> x_v)
  **  ((y_pre) # Int  |-> y_v)))
  F.

Definition exgcd_Proof_entail_Inter :=
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z),
  (“ (INT_MIN < a_pre) ”
  &&  “ (a_pre <= INT_MAX) ”
  &&  “ (INT_MIN < b_pre) ”
  &&  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_))
|--
  (“ (INT_MIN < a_pre) ”
  &&  “ (a_pre <= INT_MAX) ”
  &&  “ (INT_MIN < b_pre) ”
  &&  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_))
  **
  (ALL (retval: Z),
(orp
  (EX (y_v_2: Z) (x_v_2: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v_2 ) + (b_pre * y_v_2 ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre = 0) ”
  &&  “ ((Zabs (x_v_2)) <= 1) ”
  &&  “ (y_v_2 = 0) ”
  &&  ((x_pre) # Int  |-> x_v_2)
  **  ((y_pre) # Int  |-> y_v_2))
(orp
  (EX (y_v_3: Z) (x_v_3: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v_3 ) + (b_pre * y_v_3 ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre <> 0) ”
  &&  “ ((a_pre % ( b_pre ) ) = 0) ”
  &&  “ (x_v_3 = 0) ”
  &&  “ ((Zabs (y_v_3)) <= 1) ”
  &&  ((x_pre) # Int  |-> x_v_3)
  **  ((y_pre) # Int  |-> y_v_3))
  (EX (y_v_4: Z) (x_v_4: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v_4 ) + (b_pre * y_v_4 ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (b_pre <> 0) ”
  &&  “ ((a_pre % ( b_pre ) ) <> 0) ”
  &&  “ ((Zabs (x_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  “ ((Zabs (y_v_4)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) ”
  &&  ((x_pre) # Int  |-> x_v_4)
  **  ((y_pre) # Int  |-> y_v_4))))
  -*
  (EX (y_v: Z) (x_v: Z),
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (((a_pre * x_v ) + (b_pre * y_v ) ) = (Zgcd (a_pre) (b_pre))) ”
  &&  ((x_pre) # Int  |-> x_v)
  **  ((y_pre) # Int  |-> y_v)))
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
Axiom proof_of_exgcd_Proof_entail_Inter : exgcd_Proof_entail_Inter.

End VC_Correct.
