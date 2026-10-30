From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P083_938E_max_history_lib.
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
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (l1: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : ((Zlength (l1)) = n_pre)) (PreH5 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH6 : (Permutation values l1 )) (PreH7 : (mono_nondec l1 )),
  ((( &( "fact" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (l1: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : ((Zlength (l1)) = n_pre)) (PreH5 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH6 : (Permutation values l1 )) (PreH7 : (mono_nondec l1 )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "fact" ) )) # Int64  |-> 1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (fact: Z) (i: Z) (l1: (@list Z)) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> ((fact * i ) % ( 1000000007 ) ))
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (fact: Z) (i: Z) (l1: (@list Z)) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ (((fact * i ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (fact: Z) (i: Z) (l1: (@list Z)) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ ((fact * i ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (fact * i )) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (fact: Z) (i: Z) (l1: (@list Z)) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (fact: Z) (i: Z) (l1: (@list Z)) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (fact: Z) (i: Z) (l1: (@list Z)) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : ((Znth j l1 0) = (Znth i l1 0))) (PreH2 : (j < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH8 : (Permutation values l1 )) (PreH9 : (mono_nondec l1 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1 i )) (PreH21 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH8 : (Permutation values l1 )) (PreH9 : (mono_nondec l1 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1 i )) (PreH21 : (ContribPrefixSum l1 i total )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ False ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ False ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  ((( &( "g" ) )) # Int64  |->_)
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((n_pre - i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - i )) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((((fact % ( 1000000007 ) ) * retval ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_14 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((fact % ( 1000000007 ) ) * retval ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((fact % ( 1000000007 ) ) * retval )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((fact % ( 1000000007 ) ) * retval ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((fact % ( 1000000007 ) ) * retval )) ”
).

Definition solver_safety_wit_14_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((fact % ( 1000000007 ) ) * retval ) <= INT64_MAX) ”
.

Definition solver_safety_wit_14_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((INT64_MIN) <= ((fact % ( 1000000007 ) ) * retval )) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((fact <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((1000000007 - 2 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (1000000007 - 2 )) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((n_pre - i ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_19 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_20 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_21 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_22 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_23 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((j - i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - i )) ”
.

Definition solver_safety_wit_24 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_25 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) )) ”
).

Definition solver_safety_wit_25_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_25_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((INT64_MIN) <= (total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) )) ”
.

Definition solver_safety_wit_26 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) )) ”
).

Definition solver_safety_wit_26_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_26_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((INT64_MIN) <= (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) )) ”
.

Definition solver_safety_wit_27 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_28 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) )) ”
).

Definition solver_safety_wit_28_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_28_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((INT64_MIN) <= (((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) )) ”
.

Definition solver_safety_wit_29 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((Znth i l1 0) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_30 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((j - i ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ”
  &&  “ (1000000007 <> 0) ”
.

Definition solver_safety_wit_31 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_32 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_33 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_34 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "cnt" ) )) # Int64  |-> (j - i ))
  **  ((( &( "share" ) )) # Int64  |-> (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ))
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (1000000007 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1000000007) ”
.

Definition solver_safety_wit_35 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ))
|--
  “ ((j - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solver_safety_wit_36 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_37 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH8 : (Permutation values l1 )) (PreH9 : (mono_nondec l1 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1 i )) (PreH21 : (ContribPrefixSum l1 i total )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ ((j - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solver_safety_wit_38 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH8 : (Permutation values l1 )) (PreH9 : (mono_nondec l1 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1 i )) (PreH21 : (ContribPrefixSum l1 i total )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_39 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> (j - 1 ))
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ))
|--
  “ (((j - 1 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((j - 1 ) + 1 )) ”
.

Definition solver_safety_wit_40 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH8 : (Permutation values l1 )) (PreH9 : (mono_nondec l1 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1 i )) (PreH21 : (ContribPrefixSum l1 i total )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> (j - 1 ))
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ (((j - 1 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((j - 1 ) + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (l1_2: (@list Z)) (PreH1 : (Permutation values l1_2 )) (PreH2 : (mono_nondec l1_2 )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (values)))),
  (IntArray.full a_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  (IntArray.full a_pre n_pre l1 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (l1_2: (@list Z)) (PreH1 : (Permutation values l1_2 )) (PreH2 : (mono_nondec l1_2 )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (values)))),
  TT && emp 
|--
  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000))) ”
  &&  “ ((Zlength (l1_2)) = n_pre) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (l1_2: (@list Z)) (PreH1 : (Permutation values l1_2 )) (PreH2 : (mono_nondec l1_2 )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (values)))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (l1_2: (@list Z)) (PreH1 : (Permutation values l1_2 )) (PreH2 : (mono_nondec l1_2 )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (values)))),
  ((Zlength (l1_2)) = n_pre)
.

Definition solver_entail_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (l1_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : ((Zlength (l1_2)) = n_pre)) (PreH5 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH6 : (Permutation values l1_2 )) (PreH7 : (mono_nondec l1_2 )),
  (IntArray.full a_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= (n_pre + 1 )) ”
  &&  “ (0 <= 1) ”
  &&  “ (1 < 1000000007) ”
  &&  “ (FactorialModState 2 1 ) ”
  &&  (IntArray.full a_pre n_pre l1 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (l1_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : ((Zlength (l1_2)) = n_pre)) (PreH5 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH6 : (Permutation values l1_2 )) (PreH7 : (mono_nondec l1_2 )),
  TT && emp 
|--
  “ (FactorialModState 2 1 ) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (l1_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : ((Zlength (l1_2)) = n_pre)) (PreH5 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH6 : (Permutation values l1_2 )) (PreH7 : (mono_nondec l1_2 )),
  (FactorialModState 2 1 )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (l1_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : ((Zlength (l1_2)) = n_pre)) (PreH5 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH6 : (Permutation values l1_2 )) (PreH7 : (mono_nondec l1_2 )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))
.

Definition solver_entail_wit_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  (IntArray.full a_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (2 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ (0 <= ((fact * i ) % ( 1000000007 ) )) ”
  &&  “ (((fact * i ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (FactorialModState (i + 1 ) ((fact * i ) % ( 1000000007 ) ) ) ”
  &&  (IntArray.full a_pre n_pre l1 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  TT && emp 
|--
  “ (FactorialModState (i + 1 ) ((fact * i ) % ( 1000000007 ) ) ) ”
  &&  “ (((fact * i ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= ((fact * i ) % ( 1000000007 ) )) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  (FactorialModState (i + 1 ) ((fact * i ) % ( 1000000007 ) ) )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  (((fact * i ) % ( 1000000007 ) ) < 1000000007)
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  (0 <= ((fact * i ) % ( 1000000007 ) ))
.

Definition solver_entail_wit_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  (IntArray.full a_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= fact) ”
  &&  “ (fact < 1000000007) ”
  &&  “ (FactorialModState (n_pre + 1 ) fact ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < 1000000007) ”
  &&  “ (GroupBoundary l1 0 ) ”
  &&  “ (ContribPrefixSum l1 0 0 ) ”
  &&  (IntArray.full a_pre n_pre l1 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  TT && emp 
|--
  “ (ContribPrefixSum l1_2 0 0 ) ”
  &&  “ (GroupBoundary l1_2 0 ) ”
  &&  “ (FactorialModState (n_pre + 1 ) fact ) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  (ContribPrefixSum l1_2 0 0 )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  (GroupBoundary l1_2 0 )
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  (FactorialModState (n_pre + 1 ) fact )
.

Definition solver_entail_wit_4_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (2 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState i fact )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))
.

Definition solver_entail_wit_5 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((1 <= (Znth q_3 l1_2 0)) /\ ((Znth q_3 l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState (n_pre + 1 ) fact )) (PreH14 : (0 <= total)) (PreH15 : (total < 1000000007)) (PreH16 : (GroupBoundary l1_2 i )) (PreH17 : (ContribPrefixSum l1_2 i total )),
  (IntArray.full a_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ forall (q_2: Z), (((i <= q_2) /\ (q_2 < i)) -> ((Znth q_2 l1 0) = (Znth i l1 0))) ”
  &&  “ (0 <= fact) ”
  &&  “ (fact < 1000000007) ”
  &&  “ (FactorialModState (n_pre + 1 ) fact ) ”
  &&  “ (0 <= total) ”
  &&  “ (total < 1000000007) ”
  &&  “ (GroupBoundary l1 i ) ”
  &&  “ (ContribPrefixSum l1 i total ) ”
  &&  (IntArray.full a_pre n_pre l1 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((1 <= (Znth q_3 l1_2 0)) /\ ((Znth q_3 l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState (n_pre + 1 ) fact )) (PreH14 : (0 <= total)) (PreH15 : (total < 1000000007)) (PreH16 : (GroupBoundary l1_2 i )) (PreH17 : (ContribPrefixSum l1_2 i total )),
  TT && emp 
|--
  “ forall (q_2: Z), (((i <= q_2) /\ (q_2 < i)) -> ((Znth q_2 l1_2 0) = (Znth i l1_2 0))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((1 <= (Znth q_3 l1_2 0)) /\ ((Znth q_3 l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState (n_pre + 1 ) fact )) (PreH14 : (0 <= total)) (PreH15 : (total < 1000000007)) (PreH16 : (GroupBoundary l1_2 i )) (PreH17 : (ContribPrefixSum l1_2 i total )),
  forall (q_2: Z), (((i <= q_2) /\ (q_2 < i)) -> ((Znth q_2 l1_2 0) = (Znth i l1_2 0)))
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1_2)) = n_pre)) (PreH6 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < n_pre)) -> ((1 <= (Znth q_3 l1_2 0)) /\ ((Znth q_3 l1_2 0) <= 1000000000)))) (PreH7 : (Permutation values l1_2 )) (PreH8 : (mono_nondec l1_2 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState (n_pre + 1 ) fact )) (PreH14 : (0 <= total)) (PreH15 : (total < 1000000007)) (PreH16 : (GroupBoundary l1_2 i )) (PreH17 : (ContribPrefixSum l1_2 i total )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))
.

Definition solver_entail_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : ((Znth j l1_2 0) = (Znth i l1_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1_2)) = n_pre)) (PreH7 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))) (PreH8 : (Permutation values l1_2 )) (PreH9 : (mono_nondec l1_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1_2 0) = (Znth i l1_2 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1_2 i )) (PreH21 : (ContribPrefixSum l1_2 i total )),
  (IntArray.full a_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= n_pre) ”
  &&  “ forall (q_2: Z), (((i <= q_2) /\ (q_2 < (j + 1 ))) -> ((Znth q_2 l1 0) = (Znth i l1 0))) ”
  &&  “ (0 <= fact) ”
  &&  “ (fact < 1000000007) ”
  &&  “ (FactorialModState (n_pre + 1 ) fact ) ”
  &&  “ (0 <= total) ”
  &&  “ (total < 1000000007) ”
  &&  “ (GroupBoundary l1 i ) ”
  &&  “ (ContribPrefixSum l1 i total ) ”
  &&  (IntArray.full a_pre n_pre l1 )
.

Definition solver_entail_wit_7_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1_2 0) <> (Znth i l1_2 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1_2)) = n_pre)) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH12 : (Permutation values l1_2 )) (PreH13 : (mono_nondec l1_2 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1_2 i )) (PreH25 : (ContribPrefixSum l1_2 i total )),
  (IntArray.full a_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (0 <= ((j - 1 ) + 1 )) ”
  &&  “ (((j - 1 ) + 1 ) <= n_pre) ”
  &&  “ (0 <= fact) ”
  &&  “ (fact < 1000000007) ”
  &&  “ (FactorialModState (n_pre + 1 ) fact ) ”
  &&  “ (0 <= ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1_2 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) )) ”
  &&  “ (((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1_2 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (GroupBoundary l1 ((j - 1 ) + 1 ) ) ”
  &&  “ (ContribPrefixSum l1 ((j - 1 ) + 1 ) ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1_2 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) ) ”
  &&  (IntArray.full a_pre n_pre l1 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1_2 0) <> (Znth i l1_2 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1_2)) = n_pre)) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH12 : (Permutation values l1_2 )) (PreH13 : (mono_nondec l1_2 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1_2 i )) (PreH25 : (ContribPrefixSum l1_2 i total )),
  TT && emp 
|--
  “ (ContribPrefixSum l1_2 ((j - 1 ) + 1 ) ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1_2 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) ) ”
  &&  “ (GroupBoundary l1_2 ((j - 1 ) + 1 ) ) ”
  &&  “ (((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1_2 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1_2 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) )) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1_2 0) <> (Znth i l1_2 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1_2)) = n_pre)) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH12 : (Permutation values l1_2 )) (PreH13 : (mono_nondec l1_2 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1_2 i )) (PreH25 : (ContribPrefixSum l1_2 i total )),
  (ContribPrefixSum l1_2 ((j - 1 ) + 1 ) ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1_2 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) )
.

Definition solver_entail_wit_7_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1_2 0) <> (Znth i l1_2 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1_2)) = n_pre)) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH12 : (Permutation values l1_2 )) (PreH13 : (mono_nondec l1_2 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1_2 i )) (PreH25 : (ContribPrefixSum l1_2 i total )),
  (GroupBoundary l1_2 ((j - 1 ) + 1 ) )
.

Definition solver_entail_wit_7_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1_2 0) <> (Znth i l1_2 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1_2)) = n_pre)) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH12 : (Permutation values l1_2 )) (PreH13 : (mono_nondec l1_2 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1_2 i )) (PreH25 : (ContribPrefixSum l1_2 i total )),
  (((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1_2 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ) < 1000000007)
.

Definition solver_entail_wit_7_1_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1_2 0) <> (Znth i l1_2 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1_2)) = n_pre)) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH12 : (Permutation values l1_2 )) (PreH13 : (mono_nondec l1_2 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1_2 i )) (PreH25 : (ContribPrefixSum l1_2 i total )),
  (0 <= ((total + (((((j - i ) % ( 1000000007 ) ) * ((Znth i l1_2 0) % ( 1000000007 ) ) ) % ( 1000000007 ) ) * (((fact % ( 1000000007 ) ) * retval ) % ( 1000000007 ) ) ) ) % ( 1000000007 ) ))
.

Definition solver_entail_wit_7_1_split_goal_5 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1_2 0) <> (Znth i l1_2 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1_2)) = n_pre)) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH12 : (Permutation values l1_2 )) (PreH13 : (mono_nondec l1_2 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1_2 i )) (PreH25 : (ContribPrefixSum l1_2 i total )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))
.

Definition solver_entail_wit_7_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1_2)) = n_pre)) (PreH7 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH8 : (Permutation values l1_2 )) (PreH9 : (mono_nondec l1_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1_2 i )) (PreH21 : (ContribPrefixSum l1_2 i total )),
  (IntArray.full a_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (0 <= ((j - 1 ) + 1 )) ”
  &&  “ (((j - 1 ) + 1 ) <= n_pre) ”
  &&  “ (0 <= fact) ”
  &&  “ (fact < 1000000007) ”
  &&  “ (FactorialModState (n_pre + 1 ) fact ) ”
  &&  “ (0 <= total) ”
  &&  “ (total < 1000000007) ”
  &&  “ (GroupBoundary l1 ((j - 1 ) + 1 ) ) ”
  &&  “ (ContribPrefixSum l1 ((j - 1 ) + 1 ) total ) ”
  &&  (IntArray.full a_pre n_pre l1 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1_2)) = n_pre)) (PreH7 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH8 : (Permutation values l1_2 )) (PreH9 : (mono_nondec l1_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1_2 i )) (PreH21 : (ContribPrefixSum l1_2 i total )),
  TT && emp 
|--
  “ (ContribPrefixSum l1_2 ((j - 1 ) + 1 ) total ) ”
  &&  “ (GroupBoundary l1_2 ((j - 1 ) + 1 ) ) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1_2)) = n_pre)) (PreH7 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH8 : (Permutation values l1_2 )) (PreH9 : (mono_nondec l1_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1_2 i )) (PreH21 : (ContribPrefixSum l1_2 i total )),
  (ContribPrefixSum l1_2 ((j - 1 ) + 1 ) total )
.

Definition solver_entail_wit_7_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1_2)) = n_pre)) (PreH7 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH8 : (Permutation values l1_2 )) (PreH9 : (mono_nondec l1_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1_2 i )) (PreH21 : (ContribPrefixSum l1_2 i total )),
  (GroupBoundary l1_2 ((j - 1 ) + 1 ) )
.

Definition solver_entail_wit_7_2_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (l1_2)) = n_pre)) (PreH7 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < n_pre)) -> ((1 <= (Znth q_2 l1_2 0)) /\ ((Znth q_2 l1_2 0) <= 1000000000)))) (PreH8 : (Permutation values l1_2 )) (PreH9 : (mono_nondec l1_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (i <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (q_3: Z), (((i <= q_3) /\ (q_3 < j)) -> ((Znth q_3 l1_2 0) = (Znth i l1_2 0)))) (PreH15 : (0 <= fact)) (PreH16 : (fact < 1000000007)) (PreH17 : (FactorialModState (n_pre + 1 ) fact )) (PreH18 : (0 <= total)) (PreH19 : (total < 1000000007)) (PreH20 : (GroupBoundary l1_2 i )) (PreH21 : (ContribPrefixSum l1_2 i total )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1_2 0)) /\ ((Znth q l1_2 0) <= 1000000000)))
.

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (i: Z) (l1: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState (n_pre + 1 ) fact )) (PreH14 : (0 <= total)) (PreH15 : (total < 1000000007)) (PreH16 : (GroupBoundary l1 i )) (PreH17 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
|--
  EX (a_after: (@list Z)),
  “ (Spec values total ) ”
  &&  “ (Permutation values a_after ) ”
  &&  (IntArray.full a_pre n_pre a_after )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (i: Z) (l1: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState (n_pre + 1 ) fact )) (PreH14 : (0 <= total)) (PreH15 : (total < 1000000007)) (PreH16 : (GroupBoundary l1 i )) (PreH17 : (ContribPrefixSum l1 i total )),
  TT && emp 
|--
  “ (Spec values total ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (total: Z) (fact: Z) (i: Z) (l1: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= fact)) (PreH12 : (fact < 1000000007)) (PreH13 : (FactorialModState (n_pre + 1 ) fact )) (PreH14 : (0 <= total)) (PreH15 : (total < 1000000007)) (PreH16 : (GroupBoundary l1 i )) (PreH17 : (ContribPrefixSum l1 i total )),
  (Spec values total )
.

Definition solver_partial_solve_wit_1_pure :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (i <= j)) (PreH12 : (j <= n_pre)) (PreH13 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH14 : (0 <= fact)) (PreH15 : (fact < 1000000007)) (PreH16 : (FactorialModState (n_pre + 1 ) fact )) (PreH17 : (0 <= total)) (PreH18 : (total < 1000000007)) (PreH19 : (GroupBoundary l1 i )) (PreH20 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
|--
  “ (j < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0))) ”
  &&  “ (0 <= fact) ”
  &&  “ (fact < 1000000007) ”
  &&  “ (FactorialModState (n_pre + 1 ) fact ) ”
  &&  “ (0 <= total) ”
  &&  “ (total < 1000000007) ”
  &&  “ (GroupBoundary l1 i ) ”
  &&  “ (ContribPrefixSum l1 i total ) ”
  &&  (((a_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l1 0))
  **  (IntArray.missing_i a_pre j 0 n_pre l1 )
.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (l1)) = n_pre)) (PreH6 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH7 : (Permutation values l1 )) (PreH8 : (mono_nondec l1 )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (i <= j)) (PreH12 : (j <= n_pre)) (PreH13 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH14 : (0 <= fact)) (PreH15 : (fact < 1000000007)) (PreH16 : (FactorialModState (n_pre + 1 ) fact )) (PreH17 : (0 <= total)) (PreH18 : (total < 1000000007)) (PreH19 : (GroupBoundary l1 i )) (PreH20 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
|--
  “ (j < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0))) ”
  &&  “ (0 <= fact) ”
  &&  “ (fact < 1000000007) ”
  &&  “ (FactorialModState (n_pre + 1 ) fact ) ”
  &&  “ (0 <= total) ”
  &&  “ (total < 1000000007) ”
  &&  “ (GroupBoundary l1 i ) ”
  &&  “ (ContribPrefixSum l1 i total ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l1 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l1 )
.

Definition solver_partial_solve_wit_4_pure :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (0 <= (1000000007 - 2 )) ”
  &&  “ ((1000000007 - 2 ) <= 1000000007) ”
  &&  “ (((n_pre - i ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= ((n_pre - i ) % ( 1000000007 ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (total <= INT64_MAX)) (PreH2 : (fact <= INT64_MAX)) (PreH3 : ((n_pre - i ) <= INT64_MAX)) (PreH4 : (total >= INT64_MIN)) (PreH5 : (fact >= INT64_MIN)) (PreH6 : ((n_pre - i ) >= INT64_MIN)) (PreH7 : (j <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (j < n_pre)) (PreH14 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH15 : (j < n_pre)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 1000000)) (PreH18 : (n_pre = (Zlength (values)))) (PreH19 : ((Zlength (l1)) = n_pre)) (PreH20 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH21 : (Permutation values l1 )) (PreH22 : (mono_nondec l1 )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (i <= j)) (PreH26 : (j <= n_pre)) (PreH27 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH28 : (0 <= fact)) (PreH29 : (fact < 1000000007)) (PreH30 : (FactorialModState (n_pre + 1 ) fact )) (PreH31 : (0 <= total)) (PreH32 : (total < 1000000007)) (PreH33 : (GroupBoundary l1 i )) (PreH34 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (0 <= ((n_pre - i ) % ( 1000000007 ) )) ”
  &&  “ (((n_pre - i ) % ( 1000000007 ) ) < 1000000007) ”
).

Definition solver_partial_solve_wit_4_pure_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (total <= INT64_MAX)) (PreH2 : (fact <= INT64_MAX)) (PreH3 : ((n_pre - i ) <= INT64_MAX)) (PreH4 : (total >= INT64_MIN)) (PreH5 : (fact >= INT64_MIN)) (PreH6 : ((n_pre - i ) >= INT64_MIN)) (PreH7 : (j <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (j < n_pre)) (PreH14 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH15 : (j < n_pre)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 1000000)) (PreH18 : (n_pre = (Zlength (values)))) (PreH19 : ((Zlength (l1)) = n_pre)) (PreH20 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH21 : (Permutation values l1 )) (PreH22 : (mono_nondec l1 )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (i <= j)) (PreH26 : (j <= n_pre)) (PreH27 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH28 : (0 <= fact)) (PreH29 : (fact < 1000000007)) (PreH30 : (FactorialModState (n_pre + 1 ) fact )) (PreH31 : (0 <= total)) (PreH32 : (total < 1000000007)) (PreH33 : (GroupBoundary l1 i )) (PreH34 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (0 <= ((n_pre - i ) % ( 1000000007 ) )) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (total <= INT64_MAX)) (PreH2 : (fact <= INT64_MAX)) (PreH3 : ((n_pre - i ) <= INT64_MAX)) (PreH4 : (total >= INT64_MIN)) (PreH5 : (fact >= INT64_MIN)) (PreH6 : ((n_pre - i ) >= INT64_MIN)) (PreH7 : (j <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (j < n_pre)) (PreH14 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH15 : (j < n_pre)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 1000000)) (PreH18 : (n_pre = (Zlength (values)))) (PreH19 : ((Zlength (l1)) = n_pre)) (PreH20 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH21 : (Permutation values l1 )) (PreH22 : (mono_nondec l1 )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (i <= j)) (PreH26 : (j <= n_pre)) (PreH27 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH28 : (0 <= fact)) (PreH29 : (fact < 1000000007)) (PreH30 : (FactorialModState (n_pre + 1 ) fact )) (PreH31 : (0 <= total)) (PreH32 : (total < 1000000007)) (PreH33 : (GroupBoundary l1 i )) (PreH34 : (ContribPrefixSum l1 i total )),
  ((( &( "share" ) )) # Int64  |->_)
  **  ((( &( "g" ) )) # Int64  |-> (n_pre - i ))
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((n_pre - i ) % ( 1000000007 ) ) < 1000000007) ”
.

Definition solver_partial_solve_wit_4_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (l1)) = n_pre)) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH9 : (Permutation values l1 )) (PreH10 : (mono_nondec l1 )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH16 : (0 <= fact)) (PreH17 : (fact < 1000000007)) (PreH18 : (FactorialModState (n_pre + 1 ) fact )) (PreH19 : (0 <= total)) (PreH20 : (total < 1000000007)) (PreH21 : (GroupBoundary l1 i )) (PreH22 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
|--
  “ (0 <= (1000000007 - 2 )) ”
  &&  “ ((1000000007 - 2 ) <= 1000000007) ”
  &&  “ (((n_pre - i ) % ( 1000000007 ) ) < 1000000007) ”
  &&  “ (0 <= ((n_pre - i ) % ( 1000000007 ) )) ”
  &&  “ (j < n_pre) ”
  &&  “ ((Znth j l1 0) <> (Znth i l1 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0))) ”
  &&  “ (0 <= fact) ”
  &&  “ (fact < 1000000007) ”
  &&  “ (FactorialModState (n_pre + 1 ) fact ) ”
  &&  “ (0 <= total) ”
  &&  “ (total < 1000000007) ”
  &&  “ (GroupBoundary l1 i ) ”
  &&  “ (ContribPrefixSum l1 i total ) ”
  &&  (IntArray.full a_pre n_pre l1 )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (total: Z) (fact: Z) (j: Z) (i: Z) (l1: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 1000000007)) (PreH3 : (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval )) (PreH4 : (j < n_pre)) (PreH5 : ((Znth j l1 0) <> (Znth i l1 0))) (PreH6 : (j < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (l1)) = n_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000)))) (PreH12 : (Permutation values l1 )) (PreH13 : (mono_nondec l1 )) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= n_pre)) (PreH18 : forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0)))) (PreH19 : (0 <= fact)) (PreH20 : (fact < 1000000007)) (PreH21 : (FactorialModState (n_pre + 1 ) fact )) (PreH22 : (0 <= total)) (PreH23 : (total < 1000000007)) (PreH24 : (GroupBoundary l1 i )) (PreH25 : (ContribPrefixSum l1 i total )),
  (IntArray.full a_pre n_pre l1 )
|--
  “ (0 <= retval) ”
  &&  “ (retval < 1000000007) ”
  &&  “ (ModPower ((n_pre - i ) % ( 1000000007 ) ) (1000000007 - 2 ) retval ) ”
  &&  “ (j < n_pre) ”
  &&  “ ((Znth j l1 0) <> (Znth i l1 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q l1 0)) /\ ((Znth q l1 0) <= 1000000000))) ”
  &&  “ (Permutation values l1 ) ”
  &&  “ (mono_nondec l1 ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ forall (q_2: Z), (((i <= q_2) /\ (q_2 < j)) -> ((Znth q_2 l1 0) = (Znth i l1 0))) ”
  &&  “ (0 <= fact) ”
  &&  “ (fact < 1000000007) ”
  &&  “ (FactorialModState (n_pre + 1 ) fact ) ”
  &&  “ (0 <= total) ”
  &&  “ (total < 1000000007) ”
  &&  “ (GroupBoundary l1 i ) ”
  &&  “ (ContribPrefixSum l1 i total ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l1 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l1 )
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
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.

End VC_Correct.
