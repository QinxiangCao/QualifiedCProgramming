From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P064_223C_partial_sums_lib.
Local Open Scope sac.

(*----- Function power -----*)

Definition power_safety_wit_1 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)),
  ((( &( "r" ) )) # Int64  |->_)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "e" ) )) # Int64  |-> e_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition power_safety_wit_2 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)),
  ((( &( "r" ) )) # Int64  |-> 1)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "e" ) )) # Int64  |-> e_pre)
|--
  “ ((b_pre <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition power_safety_wit_3 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)),
  ((( &( "r" ) )) # Int64  |-> 1)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "e" ) )) # Int64  |-> e_pre)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition power_safety_wit_4 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)),
  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition power_safety_wit_5 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (((r * b ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition power_safety_wit_6 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ ((r * b ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (r * b )) ”
.

Definition power_safety_wit_7 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition power_safety_wit_8 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> ((r * b ) % ( 1000000007 ) ))
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (((b * b ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition power_safety_wit_9 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> ((r * b ) % ( 1000000007 ) ))
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ ((b * b ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (b * b )) ”
.

Definition power_safety_wit_10 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> ((r * b ) % ( 1000000007 ) ))
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition power_safety_wit_11 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (((b * b ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition power_safety_wit_12 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ ((b * b ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (b * b )) ”
.

Definition power_safety_wit_13 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition power_safety_wit_14 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  ((( &( "b" ) )) # Int64  |-> ((b * b ) % ( 1000000007 ) ))
  **  ((( &( "r" ) )) # Int64  |-> ((r * b ) % ( 1000000007 ) ))
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (0 <= e) ”
  &&  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition power_safety_wit_15 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  ((( &( "b" ) )) # Int64  |-> ((b * b ) % ( 1000000007 ) ))
  **  ((( &( "r" ) )) # Int64  |-> ((r * b ) % ( 1000000007 ) ))
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition power_safety_wit_16 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  ((( &( "b" ) )) # Int64  |-> ((b * b ) % ( 1000000007 ) ))
  **  ((( &( "r" ) )) # Int64  |-> r)
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (0 <= e) ”
  &&  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition power_safety_wit_17 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  ((( &( "b" ) )) # Int64  |-> ((b * b ) % ( 1000000007 ) ))
  **  ((( &( "r" ) )) # Int64  |-> r)
  **  ((( &( "e" ) )) # Int64  |-> e)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition power_entail_wit_1 :=
(
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)),
  TT && emp 
|--
  “ (0 <= b_pre) ”
  &&  “ (b_pre < 1000000007) ”
  &&  “ (0 <= e_pre) ”
  &&  “ (e_pre <= 1000000007) ”
  &&  “ (0 <= (b_pre % ( 1000000007 ) )) ”
  &&  “ ((b_pre % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= 1) ”
  &&  “ (1 < 1000000007) ”
  &&  “ (0 <= e_pre) ”
  &&  “ (e_pre <= e_pre) ”
  &&  “ (PowerLoopState b_pre e_pre 1 (b_pre % ( 1000000007 ) ) e_pre ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)),
  TT && emp 
|--
  “ (PowerLoopState b_pre e_pre 1 (b_pre % ( 1000000007 ) ) e_pre ) ”
  &&  “ ((b_pre % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= (b_pre % ( 1000000007 ) )) ”
  &&  emp
).

Definition power_entail_wit_1_split_goal_1 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)),
  (PowerLoopState b_pre e_pre 1 (b_pre % ( 1000000007 ) ) e_pre )
.

Definition power_entail_wit_1_split_goal_2 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)),
  ((b_pre % ( 1000000007 ) ) < 1000000007)
.

Definition power_entail_wit_1_split_goal_3 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)),
  (0 <= (b_pre % ( 1000000007 ) ))
.

Definition power_entail_wit_2_1 :=
(
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  TT && emp 
|--
  “ (0 <= b_pre) ”
  &&  “ (b_pre < 1000000007) ”
  &&  “ (0 <= e_pre) ”
  &&  “ (e_pre <= 1000000007) ”
  &&  “ (0 <= ((b * b ) % ( 1000000007 ) )) ”
  &&  “ (((b * b ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= ((r * b ) % ( 1000000007 ) )) ”
  &&  “ (((r * b ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  “ ((Z.shiftr e 1) <= e_pre) ”
  &&  “ (PowerLoopState b_pre e_pre ((r * b ) % ( 1000000007 ) ) ((b * b ) % ( 1000000007 ) ) (Z.shiftr e 1) ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  TT && emp 
|--
  “ (PowerLoopState b_pre e_pre ((r * b ) % ( 1000000007 ) ) ((b * b ) % ( 1000000007 ) ) (Z.shiftr e 1) ) ”
  &&  “ ((Z.shiftr e 1) <= e_pre) ”
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  “ (((r * b ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= ((r * b ) % ( 1000000007 ) )) ”
  &&  “ (((b * b ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= ((b * b ) % ( 1000000007 ) )) ”
  &&  emp
).

Definition power_entail_wit_2_1_split_goal_1 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  (PowerLoopState b_pre e_pre ((r * b ) % ( 1000000007 ) ) ((b * b ) % ( 1000000007 ) ) (Z.shiftr e 1) )
.

Definition power_entail_wit_2_1_split_goal_2 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  ((Z.shiftr e 1) <= e_pre)
.

Definition power_entail_wit_2_1_split_goal_3 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  (0 <= (Z.shiftr e 1))
.

Definition power_entail_wit_2_1_split_goal_4 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  (((r * b ) % ( 1000000007 ) ) < 1000000007)
.

Definition power_entail_wit_2_1_split_goal_5 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  (0 <= ((r * b ) % ( 1000000007 ) ))
.

Definition power_entail_wit_2_1_split_goal_6 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  (((b * b ) % ( 1000000007 ) ) < 1000000007)
.

Definition power_entail_wit_2_1_split_goal_7 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) <> 0)),
  (0 <= ((b * b ) % ( 1000000007 ) ))
.

Definition power_entail_wit_2_2 :=
(
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  TT && emp 
|--
  “ (0 <= b_pre) ”
  &&  “ (b_pre < 1000000007) ”
  &&  “ (0 <= e_pre) ”
  &&  “ (e_pre <= 1000000007) ”
  &&  “ (0 <= ((b * b ) % ( 1000000007 ) )) ”
  &&  “ (((b * b ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= r) ”
  &&  “ (r < 1000000007) ”
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  “ ((Z.shiftr e 1) <= e_pre) ”
  &&  “ (PowerLoopState b_pre e_pre r ((b * b ) % ( 1000000007 ) ) (Z.shiftr e 1) ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  TT && emp 
|--
  “ (PowerLoopState b_pre e_pre r ((b * b ) % ( 1000000007 ) ) (Z.shiftr e 1) ) ”
  &&  “ ((Z.shiftr e 1) <= e_pre) ”
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  “ (((b * b ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= ((b * b ) % ( 1000000007 ) )) ”
  &&  emp
).

Definition power_entail_wit_2_2_split_goal_1 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  (PowerLoopState b_pre e_pre r ((b * b ) % ( 1000000007 ) ) (Z.shiftr e 1) )
.

Definition power_entail_wit_2_2_split_goal_2 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  ((Z.shiftr e 1) <= e_pre)
.

Definition power_entail_wit_2_2_split_goal_3 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  (0 <= (Z.shiftr e 1))
.

Definition power_entail_wit_2_2_split_goal_4 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  (((b * b ) % ( 1000000007 ) ) < 1000000007)
.

Definition power_entail_wit_2_2_split_goal_5 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e <> 0)) (PreH13 : ((Z.land e 1) = 0)),
  (0 <= ((b * b ) % ( 1000000007 ) ))
.

Definition power_return_wit_1 :=
(
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e = 0)),
  TT && emp 
|--
  “ (0 <= r) ”
  &&  “ (r < 1000000007) ”
  &&  “ (ModPower b_pre e_pre r ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e = 0)),
  TT && emp 
|--
  “ (ModPower b_pre e_pre r ) ”
  &&  emp
).

Definition power_return_wit_1_split_goal_1 :=
forall (b_pre: Z) (e_pre: Z) (e: Z) (r: Z) (b: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 1000000007)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 1000000007)) (PreH5 : (0 <= b)) (PreH6 : (b < 1000000007)) (PreH7 : (0 <= r)) (PreH8 : (r < 1000000007)) (PreH9 : (0 <= e)) (PreH10 : (e <= e_pre)) (PreH11 : (PowerLoopState b_pre e_pre r b e )) (PreH12 : (e = 0)),
  (ModPower b_pre e_pre r )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (values)))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (PreH1 : (k_pre = 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written)) = i)) (PreH10 : (IdentityPrefix values written )),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (written) ((cons (((Znth i values 0) % ( 1000000007 ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written)) = i)) (PreH10 : (IdentityPrefix values written )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  “ (((Znth i values 0) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written)) = i)) (PreH10 : (IdentityPrefix values written )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (PreH1 : (k_pre <> 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (PreH1 : (k_pre <> 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (PreH1 : (k_pre <> 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  ((( &( "d" ) )) # Int  |->_)
  **  (((coef_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
  **  (Int64Array.undef_seg coef_pre 1 n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients)) = d)) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 (d + 1 ) (app (coefficients) ((cons (((((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) % ( 1000000007 ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg coef_pre (d + 1 ) n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
|--
  “ ((d + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients)) = d)) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (((((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_11 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients)) = d)) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients)) = d)) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval )) ”
).

Definition solver_safety_wit_11_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients)) = d)) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) <= INT64_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients)) = d)) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((INT64_MIN) <= (((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval )) ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_13 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) )) ”
).

Definition solver_safety_wit_13_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_13_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((INT64_MIN) <= (((Znth ((d - 1 ) - 0 ) coefficients 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) )) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((((k_pre - 1 ) + d ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (((k_pre - 1 ) + d ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((k_pre - 1 ) + d )) ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((k_pre - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (k_pre - 1 )) ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (((Znth ((d - 1 ) - 0 ) coefficients 0) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.seg coef_pre 0 d coefficients )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((d - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (d - 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.seg coef_pre 0 d coefficients )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_20 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_21 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_23 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_24 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ ((1000000007 - 2 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (1000000007 - 2 )) ”
.

Definition solver_safety_wit_25 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_26 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_27 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients)) = d)) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_28 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (d >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients)) = d)) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.seg coef_pre 0 d coefficients )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_29 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )),
  ((( &( "s" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_30 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_31 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> ((s + ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ))
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_32 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (((s + ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_33 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((s + ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s + ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((s + ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s + ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) )) ”
).

Definition solver_safety_wit_33_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((s + ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_33_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((INT64_MIN) <= (s + ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) )) ”
.

Definition solver_safety_wit_34 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) )) ”
).

Definition solver_safety_wit_34_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_34_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((INT64_MIN) <= ((Znth (i - j ) coefficients 0) * ((Znth j values 0) % ( 1000000007 ) ) )) ”
.

Definition solver_safety_wit_35 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (((Znth j values 0) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_36 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((i - j ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - j )) ”
.

Definition solver_safety_wit_37 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_38 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_39 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j > i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (written) ((cons (s) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (PreH1 : (k_pre = 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  EX (written: (@list Z)),
  “ (k_pre = 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (written)) = 0) ”
  &&  “ (IdentityPrefix values written ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg out_pre 0 0 written )
  **  (Int64Array.undef_seg out_pre 0 n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre = 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  TT && emp 
|--
  “ (IdentityPrefix values (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre = 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  (IdentityPrefix values (@nil Z) )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre = 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre = 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))
.

Definition solver_entail_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written_2)) = i)) (PreH10 : (IdentityPrefix values written_2 )),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (written_2) ((cons (((Znth i values 0) % ( 1000000007 ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  EX (written: (@list Z)),
  “ (k_pre = 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (written)) = (i + 1 )) ”
  &&  “ (IdentityPrefix values written ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg out_pre 0 (i + 1 ) written )
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (written_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written_2)) = i)) (PreH10 : (IdentityPrefix values written_2 )),
  TT && emp 
|--
  “ (IdentityPrefix values (app (written_2) ((cons (((Znth i values 0) % ( 1000000007 ) )) ((@nil Z))))) ) ”
  &&  “ ((Zlength ((app (written_2) ((cons (((Znth i values 0) % ( 1000000007 ) )) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (written_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written_2)) = i)) (PreH10 : (IdentityPrefix values written_2 )),
  (IdentityPrefix values (app (written_2) ((cons (((Znth i values 0) % ( 1000000007 ) )) ((@nil Z))))) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (written_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written_2)) = i)) (PreH10 : (IdentityPrefix values written_2 )),
  ((Zlength ((app (written_2) ((cons (((Znth i values 0) % ( 1000000007 ) )) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (PreH1 : (k_pre <> 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  (((coef_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
  **  (Int64Array.undef_seg coef_pre 1 n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
|--
  EX (coefficients: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= n_pre) ”
  &&  “ ((Zlength (coefficients)) = 1) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < 1)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.seg coef_pre 0 1 coefficients )
  **  (Int64Array.undef_seg coef_pre 1 n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coef_pre: Z) (PreH1 : (1 <= INT64_MAX)) (PreH2 : (1 >= INT64_MIN)) (PreH3 : (k_pre <> 0)) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (values)))),
  (((coef_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
|--
  EX (coefficients: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= n_pre) ”
  &&  “ ((Zlength (coefficients)) = 1) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < 1)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  (Int64Array.seg coef_pre 0 1 coefficients )
).

Definition solver_entail_wit_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients_2: (@list Z)) (d: Z) (PreH1 : (d < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients_2)) = d)) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients_2 )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.seg coef_pre 0 d coefficients_2 )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  EX (coefficients: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (1 <= d) ”
  &&  “ (d < n_pre) ”
  &&  “ ((Zlength (coefficients)) = d) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.seg coef_pre 0 d coefficients )
  **  (Int64Array.undef_seg coef_pre d n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (PreH1 : (d < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients_2)) = d)) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients_2 )),
  TT && emp 
|--
  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (PreH1 : (d < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients_2)) = d)) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients_2 )),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007)))
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (PreH1 : (d < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients_2)) = d)) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients_2 )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))
.

Definition solver_entail_wit_5 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients_2: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients_2)) = d)) (PreH13 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients_2 )),
  (Int64Array.seg coef_pre 0 (d + 1 ) (app (coefficients_2) ((cons (((((((Znth ((d - 1 ) - 0 ) coefficients_2 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) % ( 1000000007 ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg coef_pre (d + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
|--
  EX (coefficients: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (1 <= (d + 1 )) ”
  &&  “ ((d + 1 ) <= n_pre) ”
  &&  “ ((Zlength (coefficients)) = (d + 1 )) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (d + 1 ))) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.seg coef_pre 0 (d + 1 ) coefficients )
  **  (Int64Array.undef_seg coef_pre (d + 1 ) n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients_2)) = d)) (PreH13 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients_2 )),
  TT && emp 
|--
  “ (CoefficientPrefix k_pre (app (coefficients_2) ((cons (((((((Znth ((d - 1 ) - 0 ) coefficients_2 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) % ( 1000000007 ) )) ((@nil Z))))) ) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (d + 1 ))) -> ((0 <= (Znth q_2 (app (coefficients_2) ((cons (((((((Znth ((d - 1 ) - 0 ) coefficients_2 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) % ( 1000000007 ) )) ((@nil Z))))) 0)) /\ ((Znth q_2 (app (coefficients_2) ((cons (((((((Znth ((d - 1 ) - 0 ) coefficients_2 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) % ( 1000000007 ) )) ((@nil Z))))) 0) < 1000000007))) ”
  &&  “ ((Zlength ((app (coefficients_2) ((cons (((((((Znth ((d - 1 ) - 0 ) coefficients_2 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) % ( 1000000007 ) )) ((@nil Z))))))) = (d + 1 )) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients_2)) = d)) (PreH13 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients_2 )),
  (CoefficientPrefix k_pre (app (coefficients_2) ((cons (((((((Znth ((d - 1 ) - 0 ) coefficients_2 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) % ( 1000000007 ) )) ((@nil Z))))) )
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients_2)) = d)) (PreH13 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients_2 )),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (d + 1 ))) -> ((0 <= (Znth q_2 (app (coefficients_2) ((cons (((((((Znth ((d - 1 ) - 0 ) coefficients_2 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) % ( 1000000007 ) )) ((@nil Z))))) 0)) /\ ((Znth q_2 (app (coefficients_2) ((cons (((((((Znth ((d - 1 ) - 0 ) coefficients_2 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) % ( 1000000007 ) )) ((@nil Z))))) 0) < 1000000007)))
.

Definition solver_entail_wit_5_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients_2)) = d)) (PreH13 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients_2 )),
  ((Zlength ((app (coefficients_2) ((cons (((((((Znth ((d - 1 ) - 0 ) coefficients_2 0) % ( 1000000007 ) ) * (((k_pre - 1 ) + d ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * retval ) % ( 1000000007 ) )) ((@nil Z))))))) = (d + 1 ))
.

Definition solver_entail_wit_5_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients_2)) = d)) (PreH13 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients_2 )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))
.

Definition solver_entail_wit_6 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients_2: (@list Z)) (d: Z) (PreH1 : (d >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients_2)) = d)) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients_2 )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.seg coef_pre 0 d coefficients_2 )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  EX (written: (@list Z)) (coefficients: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ ((Zlength (coefficients)) = n_pre) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (written)) = 0) ”
  &&  “ (ConvolutionPrefix values coefficients written ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 0 written )
  **  (Int64Array.undef_seg out_pre 0 n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (PreH1 : (d >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients_2)) = d)) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients_2 )),
  TT && emp 
|--
  “ (ConvolutionPrefix values coefficients_2 (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (PreH1 : (d >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients_2)) = d)) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients_2 )),
  (ConvolutionPrefix values coefficients_2 (@nil Z) )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (PreH1 : (d >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients_2)) = d)) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients_2 )),
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_6_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (PreH1 : (d >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients_2)) = d)) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients_2 )),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007)))
.

Definition solver_entail_wit_6_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coefficients_2: (@list Z)) (d: Z) (PreH1 : (d >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : (1 <= d)) (PreH9 : (d <= n_pre)) (PreH10 : ((Zlength (coefficients_2)) = d)) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < d)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH12 : (CoefficientPrefix k_pre coefficients_2 )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))
.

Definition solver_entail_wit_7 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients_2 )
  **  (Int64Array.seg out_pre 0 i written_2 )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  EX (written: (@list Z)) (coefficients: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ ((Zlength (coefficients)) = n_pre) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (written)) = i) ”
  &&  “ (ConvolutionPrefix values coefficients written ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < 1000000007) ”
  &&  “ (ConvolutionAccumulator values coefficients i 0 0 ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )),
  TT && emp 
|--
  “ (ConvolutionAccumulator values coefficients_2 i 0 0 ) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )),
  (ConvolutionAccumulator values coefficients_2 i 0 0 )
.

Definition solver_entail_wit_7_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007)))
.

Definition solver_entail_wit_7_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))
.

Definition solver_entail_wit_8 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients_2 )
  **  (Int64Array.seg out_pre 0 i written_2 )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  EX (written: (@list Z)) (coefficients: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ ((Zlength (coefficients)) = n_pre) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (written)) = i) ”
  &&  “ (ConvolutionPrefix values coefficients written ) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (i + 1 )) ”
  &&  “ (0 <= ((s + ((Znth (i - j ) coefficients_2 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) % ( 1000000007 ) )) ”
  &&  “ (((s + ((Znth (i - j ) coefficients_2 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (ConvolutionAccumulator values coefficients i (j + 1 ) ((s + ((Znth (i - j ) coefficients_2 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  TT && emp 
|--
  “ (ConvolutionAccumulator values coefficients_2 i (j + 1 ) ((s + ((Znth (i - j ) coefficients_2 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) ) ”
  &&  “ (((s + ((Znth (i - j ) coefficients_2 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= ((s + ((Znth (i - j ) coefficients_2 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) % ( 1000000007 ) )) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  (ConvolutionAccumulator values coefficients_2 i (j + 1 ) ((s + ((Znth (i - j ) coefficients_2 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) )
.

Definition solver_entail_wit_8_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  (((s + ((Znth (i - j ) coefficients_2 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) < 1000000007)
.

Definition solver_entail_wit_8_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  (0 <= ((s + ((Znth (i - j ) coefficients_2 0) * ((Znth j values 0) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ))
.

Definition solver_entail_wit_9 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j > i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (written_2) ((cons (s) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients_2 )
|--
  EX (written: (@list Z)) (coefficients: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ ((Zlength (coefficients)) = n_pre) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (written)) = (i + 1 )) ”
  &&  “ (ConvolutionPrefix values coefficients written ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 (i + 1 ) written )
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j > i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  TT && emp 
|--
  “ (ConvolutionPrefix values coefficients_2 (app (written_2) ((cons (s) ((@nil Z))))) ) ”
  &&  “ ((Zlength ((app (written_2) ((cons (s) ((@nil Z))))))) = (i + 1 )) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j > i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  (ConvolutionPrefix values coefficients_2 (app (written_2) ((cons (s) ((@nil Z))))) )
.

Definition solver_entail_wit_9_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j > i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  ((Zlength ((app (written_2) ((cons (s) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_9_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j > i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients_2 0)) /\ ((Znth q_2 coefficients_2 0) < 1000000007)))
.

Definition solver_entail_wit_9_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (s: Z) (j: Z) (written_2: (@list Z)) (i: Z) (coefficients_2: (@list Z)) (PreH1 : (j > i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((0 <= (Znth q_3 values 0)) /\ ((Znth q_3 values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients_2)) = n_pre)) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((0 <= (Znth q_4 coefficients_2 0)) /\ ((Znth q_4 coefficients_2 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written_2)) = i)) (PreH14 : (ConvolutionPrefix values coefficients_2 written_2 )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients_2 i j s )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))
.

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written)) = i)) (PreH10 : (IdentityPrefix values written )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  EX (out_spec: (@list Z)),
  “ (Spec k_pre values out_spec ) ”
  &&  “ (k_pre = 0) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full out_pre n_pre out_spec )
  **  (Int64Array.undef_full coef_pre n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written)) = i)) (PreH10 : (IdentityPrefix values written )),
  TT && emp 
|--
  “ (Spec 0 values written ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written)) = i)) (PreH10 : (IdentityPrefix values written )),
  (Spec 0 values written )
.

Definition solver_return_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  EX (out_spec: (@list Z)),
  “ (Spec k_pre values out_spec ) ”
  &&  “ (k_pre <> 0) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full out_pre n_pre out_spec )
  **  (Int64Array.full_shape coef_pre n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )),
  (Int64Array.full coef_pre n_pre coefficients )
|--
  “ (Spec k_pre values written ) ”
  &&  (Int64Array.full_shape coef_pre n_pre )
).

Definition solver_return_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )),
  (Int64Array.full coef_pre n_pre coefficients )
|--
  “ (Spec k_pre values written ) ”
.

Definition solver_return_wit_2_split_goal_spatial :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )),
  (Int64Array.full coef_pre n_pre coefficients )
|--
  (Int64Array.full_shape coef_pre n_pre )
.

Definition solver_partial_solve_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written)) = i)) (PreH10 : (IdentityPrefix values written )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (k_pre = 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (written)) = i) ”
  &&  “ (IdentityPrefix values written ) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (k_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (written)) = i)) (PreH10 : (IdentityPrefix values written )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (k_pre = 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (written)) = i) ”
  &&  “ (IdentityPrefix values written ) ”
  &&  (((out_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_full coef_pre n_pre )
.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (PreH1 : (k_pre <> 0)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_full coef_pre n_pre )
|--
  “ (k_pre <> 0) ”
  &&  “ (0 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (((coef_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg coef_pre 1 n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
.

Definition solver_partial_solve_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.seg coef_pre 0 d coefficients )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (1 <= d) ”
  &&  “ (d < n_pre) ”
  &&  “ ((Zlength (coefficients)) = d) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  (((coef_pre + ((d - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((d - 1 ) - 0 ) coefficients 0))
  **  (Int64Array.missing_i coef_pre (d - 1 ) 0 d coefficients )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
.

Definition solver_partial_solve_wit_5_pure :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "coef" ) )) # Ptr  |-> coef_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (0 <= d) ”
  &&  “ (d < 1000000007) ”
  &&  “ (0 <= (1000000007 - 2 )) ”
  &&  “ ((1000000007 - 2 ) <= 1000000007) ”
.

Definition solver_partial_solve_wit_5_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH7 : (1 <= d)) (PreH8 : (d < n_pre)) (PreH9 : ((Zlength (coefficients)) = d)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH11 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (0 <= d) ”
  &&  “ (d < 1000000007) ”
  &&  “ (0 <= (1000000007 - 2 )) ”
  &&  “ ((1000000007 - 2 ) <= 1000000007) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (1 <= d) ”
  &&  “ (d < n_pre) ”
  &&  “ ((Zlength (coefficients)) = d) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  (Int64Array.seg coef_pre 0 d coefficients )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
.

Definition solver_partial_solve_wit_5 := solver_partial_solve_wit_5_pure -> solver_partial_solve_wit_5_aux.

Definition solver_partial_solve_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (coefficients: (@list Z)) (d: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower d (1000000007 - 2 ) retval )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH10 : (1 <= d)) (PreH11 : (d < n_pre)) (PreH12 : ((Zlength (coefficients)) = d)) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH14 : (CoefficientPrefix k_pre coefficients )),
  (Int64Array.seg coef_pre 0 d coefficients )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
  **  (Int64Array.undef_seg coef_pre d n_pre )
|--
  “ (0 <= retval) ”
  &&  “ (retval < 1000000007) ”
  &&  “ (ModPower d (1000000007 - 2 ) retval ) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ (1 <= d) ”
  &&  “ (d < n_pre) ”
  &&  “ ((Zlength (coefficients)) = d) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < d)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  (((coef_pre + (d * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg coef_pre (d + 1 ) n_pre )
  **  (Int64Array.seg coef_pre 0 d coefficients )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full out_pre n_pre )
.

Definition solver_partial_solve_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (j <= i) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ ((Zlength (coefficients)) = n_pre) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (written)) = i) ”
  &&  “ (ConvolutionPrefix values coefficients written ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (i + 1 )) ”
  &&  “ (0 <= s) ”
  &&  “ (s < 1000000007) ”
  &&  “ (ConvolutionAccumulator values coefficients i j s ) ”
  &&  (((coef_pre + ((i - j ) * sizeof(INT64)))) # Int64  |-> (Znth (i - j ) coefficients 0))
  **  (Int64Array.missing_i coef_pre (i - j ) 0 n_pre coefficients )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
.

Definition solver_partial_solve_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j <= i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (j <= i) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ ((Zlength (coefficients)) = n_pre) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (written)) = i) ”
  &&  “ (ConvolutionPrefix values coefficients written ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (i + 1 )) ”
  &&  “ (0 <= s) ”
  &&  “ (s < 1000000007) ”
  &&  “ (ConvolutionAccumulator values coefficients i j s ) ”
  &&  (((a_pre + (j * sizeof(INT64)))) # Int64  |-> (Znth j values 0))
  **  (Int64Array.missing_i a_pre j 0 n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
.

Definition solver_partial_solve_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (coef_pre: Z) (s: Z) (j: Z) (written: (@list Z)) (i: Z) (coefficients: (@list Z)) (PreH1 : (j > i)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000)))) (PreH8 : ((Zlength (coefficients)) = n_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007)))) (PreH10 : (CoefficientPrefix k_pre coefficients )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (written)) = i)) (PreH14 : (ConvolutionPrefix values coefficients written )) (PreH15 : (0 <= j)) (PreH16 : (j <= (i + 1 ))) (PreH17 : (0 <= s)) (PreH18 : (s < 1000000007)) (PreH19 : (ConvolutionAccumulator values coefficients i j s )),
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (j > i) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((0 <= (Znth q values 0)) /\ ((Znth q values 0) <= 1000000000))) ”
  &&  “ ((Zlength (coefficients)) = n_pre) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((0 <= (Znth q_2 coefficients 0)) /\ ((Znth q_2 coefficients 0) < 1000000007))) ”
  &&  “ (CoefficientPrefix k_pre coefficients ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (written)) = i) ”
  &&  “ (ConvolutionPrefix values coefficients written ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (i + 1 )) ”
  &&  “ (0 <= s) ”
  &&  “ (s < 1000000007) ”
  &&  “ (ConvolutionAccumulator values coefficients i j s ) ”
  &&  (((out_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full coef_pre n_pre coefficients )
  **  (Int64Array.seg out_pre 0 i written )
.

Module Type VC_Correct.


Axiom proof_of_power_safety_wit_1 : power_safety_wit_1.
Axiom proof_of_power_safety_wit_2 : power_safety_wit_2.
Axiom proof_of_power_safety_wit_3 : power_safety_wit_3.
Axiom proof_of_power_safety_wit_4 : power_safety_wit_4.
Axiom proof_of_power_safety_wit_5 : power_safety_wit_5.
Axiom proof_of_power_safety_wit_6 : power_safety_wit_6.
Axiom proof_of_power_safety_wit_7 : power_safety_wit_7.
Axiom proof_of_power_safety_wit_8 : power_safety_wit_8.
Axiom proof_of_power_safety_wit_9 : power_safety_wit_9.
Axiom proof_of_power_safety_wit_10 : power_safety_wit_10.
Axiom proof_of_power_safety_wit_11 : power_safety_wit_11.
Axiom proof_of_power_safety_wit_12 : power_safety_wit_12.
Axiom proof_of_power_safety_wit_13 : power_safety_wit_13.
Axiom proof_of_power_safety_wit_14 : power_safety_wit_14.
Axiom proof_of_power_safety_wit_15 : power_safety_wit_15.
Axiom proof_of_power_safety_wit_16 : power_safety_wit_16.
Axiom proof_of_power_safety_wit_17 : power_safety_wit_17.
Axiom proof_of_power_entail_wit_1 : power_entail_wit_1.
Axiom proof_of_power_entail_wit_2_1 : power_entail_wit_2_1.
Axiom proof_of_power_entail_wit_2_2 : power_entail_wit_2_2.
Axiom proof_of_power_return_wit_1 : power_return_wit_1.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.

End VC_Correct.
