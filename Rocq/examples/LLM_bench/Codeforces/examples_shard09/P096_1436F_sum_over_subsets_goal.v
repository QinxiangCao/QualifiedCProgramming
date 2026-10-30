From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P096_1436F_sum_over_subsets_lib.
Local Open Scope sac.

(*----- Function powmod -----*)

Definition powmod_safety_wit_1 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 998244353)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 100000000000000)),
  ((( &( "r" ) )) # Int64  |->_)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "e" ) )) # Int64  |-> e_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition powmod_safety_wit_2 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 998244353)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 100000000000000)),
  ((( &( "r" ) )) # Int64  |-> 1)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "e" ) )) # Int64  |-> e_pre)
|--
  “ ((b_pre <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition powmod_safety_wit_3 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 998244353)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 100000000000000)),
  ((( &( "r" ) )) # Int64  |-> 1)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "e" ) )) # Int64  |-> e_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition powmod_safety_wit_4 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : (0 <= b_pre)) (PreH2 : (b_pre < 998244353)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 100000000000000)),
  ((( &( "r" ) )) # Int64  |-> 1)
  **  ((( &( "b" ) )) # Int64  |-> (b_pre % ( 998244353 ) ))
  **  ((( &( "e" ) )) # Int64  |-> e_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition powmod_safety_wit_5 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : ((b_pre % ( 998244353 ) ) < 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre < 998244353)) (PreH4 : (0 <= e_pre)) (PreH5 : (e_pre <= 100000000000000)),
  ((( &( "r" ) )) # Int64  |-> 1)
  **  ((( &( "b" ) )) # Int64  |-> (b_pre % ( 998244353 ) ))
  **  ((( &( "e" ) )) # Int64  |-> e_pre)
|--
  “ (((b_pre % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((b_pre % ( 998244353 ) ) + 998244353 )) ”
.

Definition powmod_safety_wit_6 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : ((b_pre % ( 998244353 ) ) < 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre < 998244353)) (PreH4 : (0 <= e_pre)) (PreH5 : (e_pre <= 100000000000000)),
  ((( &( "r" ) )) # Int64  |-> 1)
  **  ((( &( "b" ) )) # Int64  |-> (b_pre % ( 998244353 ) ))
  **  ((( &( "e" ) )) # Int64  |-> e_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition powmod_safety_wit_7 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= 100000000000000)) (PreH3 : (0 <= b)) (PreH4 : (b < 998244353)) (PreH5 : (0 <= r)) (PreH6 : (r < 998244353)) (PreH7 : (PowmodState b_pre e_pre b e r )),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition powmod_safety_wit_8 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition powmod_safety_wit_9 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (((r * b ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition powmod_safety_wit_10 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ ((r * b ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (r * b )) ”
.

Definition powmod_safety_wit_11 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition powmod_safety_wit_12 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> ((r * b ) % ( 998244353 ) ))
|--
  “ (((b * b ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition powmod_safety_wit_13 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> ((r * b ) % ( 998244353 ) ))
|--
  “ ((b * b ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (b * b )) ”
.

Definition powmod_safety_wit_14 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> ((r * b ) % ( 998244353 ) ))
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition powmod_safety_wit_15 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (((b * b ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition powmod_safety_wit_16 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ ((b * b ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (b * b )) ”
.

Definition powmod_safety_wit_17 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> b)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition powmod_safety_wit_18 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> ((b * b ) % ( 998244353 ) ))
  **  ((( &( "r" ) )) # Int64  |-> ((r * b ) % ( 998244353 ) ))
|--
  “ (0 <= e) ”
  &&  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition powmod_safety_wit_19 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> ((b * b ) % ( 998244353 ) ))
  **  ((( &( "r" ) )) # Int64  |-> ((r * b ) % ( 998244353 ) ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition powmod_safety_wit_20 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> ((b * b ) % ( 998244353 ) ))
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (0 <= e) ”
  &&  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition powmod_safety_wit_21 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "b" ) )) # Int64  |-> ((b * b ) % ( 998244353 ) ))
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition powmod_entail_wit_1_1 :=
(
forall (b_pre: Z) (e_pre: Z) (PreH1 : ((b_pre % ( 998244353 ) ) < 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre < 998244353)) (PreH4 : (0 <= e_pre)) (PreH5 : (e_pre <= 100000000000000)),
  TT && emp 
|--
  “ (0 <= e_pre) ”
  &&  “ (e_pre <= 100000000000000) ”
  &&  “ (0 <= ((b_pre % ( 998244353 ) ) + 998244353 )) ”
  &&  “ (((b_pre % ( 998244353 ) ) + 998244353 ) < 998244353) ”
  &&  “ (0 <= 1) ”
  &&  “ (1 < 998244353) ”
  &&  “ (PowmodState b_pre e_pre ((b_pre % ( 998244353 ) ) + 998244353 ) e_pre 1 ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (e_pre: Z) (PreH1 : ((b_pre % ( 998244353 ) ) < 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre < 998244353)) (PreH4 : (0 <= e_pre)) (PreH5 : (e_pre <= 100000000000000)),
  TT && emp 
|--
  “ (PowmodState b_pre e_pre ((b_pre % ( 998244353 ) ) + 998244353 ) e_pre 1 ) ”
  &&  “ (0 <= ((b_pre % ( 998244353 ) ) + 998244353 )) ”
  &&  emp
).

Definition powmod_entail_wit_1_1_split_goal_1 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : ((b_pre % ( 998244353 ) ) < 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre < 998244353)) (PreH4 : (0 <= e_pre)) (PreH5 : (e_pre <= 100000000000000)),
  (PowmodState b_pre e_pre ((b_pre % ( 998244353 ) ) + 998244353 ) e_pre 1 )
.

Definition powmod_entail_wit_1_1_split_goal_2 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : ((b_pre % ( 998244353 ) ) < 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre < 998244353)) (PreH4 : (0 <= e_pre)) (PreH5 : (e_pre <= 100000000000000)),
  (0 <= ((b_pre % ( 998244353 ) ) + 998244353 ))
.

Definition powmod_entail_wit_1_2 :=
(
forall (b_pre: Z) (e_pre: Z) (PreH1 : ((b_pre % ( 998244353 ) ) >= 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre < 998244353)) (PreH4 : (0 <= e_pre)) (PreH5 : (e_pre <= 100000000000000)),
  TT && emp 
|--
  “ (0 <= e_pre) ”
  &&  “ (e_pre <= 100000000000000) ”
  &&  “ (0 <= (b_pre % ( 998244353 ) )) ”
  &&  “ ((b_pre % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= 1) ”
  &&  “ (1 < 998244353) ”
  &&  “ (PowmodState b_pre e_pre (b_pre % ( 998244353 ) ) e_pre 1 ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (e_pre: Z) (PreH1 : ((b_pre % ( 998244353 ) ) >= 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre < 998244353)) (PreH4 : (0 <= e_pre)) (PreH5 : (e_pre <= 100000000000000)),
  TT && emp 
|--
  “ (PowmodState b_pre e_pre (b_pre % ( 998244353 ) ) e_pre 1 ) ”
  &&  “ ((b_pre % ( 998244353 ) ) < 998244353) ”
  &&  emp
).

Definition powmod_entail_wit_1_2_split_goal_1 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : ((b_pre % ( 998244353 ) ) >= 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre < 998244353)) (PreH4 : (0 <= e_pre)) (PreH5 : (e_pre <= 100000000000000)),
  (PowmodState b_pre e_pre (b_pre % ( 998244353 ) ) e_pre 1 )
.

Definition powmod_entail_wit_1_2_split_goal_2 :=
forall (b_pre: Z) (e_pre: Z) (PreH1 : ((b_pre % ( 998244353 ) ) >= 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre < 998244353)) (PreH4 : (0 <= e_pre)) (PreH5 : (e_pre <= 100000000000000)),
  ((b_pre % ( 998244353 ) ) < 998244353)
.

Definition powmod_entail_wit_2_1 :=
(
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  TT && emp 
|--
  “ (0 <= (Z.shiftr e 1)) ”
  &&  “ ((Z.shiftr e 1) <= 100000000000000) ”
  &&  “ (0 <= ((b * b ) % ( 998244353 ) )) ”
  &&  “ (((b * b ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= ((r * b ) % ( 998244353 ) )) ”
  &&  “ (((r * b ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (PowmodState b_pre e_pre ((b * b ) % ( 998244353 ) ) (Z.shiftr e 1) ((r * b ) % ( 998244353 ) ) ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  TT && emp 
|--
  “ (PowmodState b_pre e_pre ((b * b ) % ( 998244353 ) ) (Z.shiftr e 1) ((r * b ) % ( 998244353 ) ) ) ”
  &&  “ (((r * b ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= ((r * b ) % ( 998244353 ) )) ”
  &&  “ (((b * b ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= ((b * b ) % ( 998244353 ) )) ”
  &&  “ ((Z.shiftr e 1) <= 100000000000000) ”
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  emp
).

Definition powmod_entail_wit_2_1_split_goal_1 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  (PowmodState b_pre e_pre ((b * b ) % ( 998244353 ) ) (Z.shiftr e 1) ((r * b ) % ( 998244353 ) ) )
.

Definition powmod_entail_wit_2_1_split_goal_2 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  (((r * b ) % ( 998244353 ) ) < 998244353)
.

Definition powmod_entail_wit_2_1_split_goal_3 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  (0 <= ((r * b ) % ( 998244353 ) ))
.

Definition powmod_entail_wit_2_1_split_goal_4 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  (((b * b ) % ( 998244353 ) ) < 998244353)
.

Definition powmod_entail_wit_2_1_split_goal_5 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  (0 <= ((b * b ) % ( 998244353 ) ))
.

Definition powmod_entail_wit_2_1_split_goal_6 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  ((Z.shiftr e 1) <= 100000000000000)
.

Definition powmod_entail_wit_2_1_split_goal_7 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) <> 0)),
  (0 <= (Z.shiftr e 1))
.

Definition powmod_entail_wit_2_2 :=
(
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  TT && emp 
|--
  “ (0 <= (Z.shiftr e 1)) ”
  &&  “ ((Z.shiftr e 1) <= 100000000000000) ”
  &&  “ (0 <= ((b * b ) % ( 998244353 ) )) ”
  &&  “ (((b * b ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= r) ”
  &&  “ (r < 998244353) ”
  &&  “ (PowmodState b_pre e_pre ((b * b ) % ( 998244353 ) ) (Z.shiftr e 1) r ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  TT && emp 
|--
  “ (PowmodState b_pre e_pre ((b * b ) % ( 998244353 ) ) (Z.shiftr e 1) r ) ”
  &&  “ (((b * b ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= ((b * b ) % ( 998244353 ) )) ”
  &&  “ ((Z.shiftr e 1) <= 100000000000000) ”
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  emp
).

Definition powmod_entail_wit_2_2_split_goal_1 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  (PowmodState b_pre e_pre ((b * b ) % ( 998244353 ) ) (Z.shiftr e 1) r )
.

Definition powmod_entail_wit_2_2_split_goal_2 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  (((b * b ) % ( 998244353 ) ) < 998244353)
.

Definition powmod_entail_wit_2_2_split_goal_3 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  (0 <= ((b * b ) % ( 998244353 ) ))
.

Definition powmod_entail_wit_2_2_split_goal_4 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  ((Z.shiftr e 1) <= 100000000000000)
.

Definition powmod_entail_wit_2_2_split_goal_5 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )) (PreH9 : ((Z.land e 1) = 0)),
  (0 <= (Z.shiftr e 1))
.

Definition powmod_return_wit_1 :=
(
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e <= 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )),
  TT && emp 
|--
  “ (r = (pow_mod (b_pre) (e_pre))) ”
  &&  “ (0 <= r) ”
  &&  “ (r < 998244353) ”
  &&  emp
) \/
(
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e <= 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )),
  TT && emp 
|--
  “ (r = (pow_mod (b_pre) (e_pre))) ”
  &&  emp
).

Definition powmod_return_wit_1_split_goal_1 :=
forall (b_pre: Z) (e_pre: Z) (r: Z) (b: Z) (e: Z) (PreH1 : (e <= 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= 100000000000000)) (PreH4 : (0 <= b)) (PreH5 : (b < 998244353)) (PreH6 : (0 <= r)) (PreH7 : (r < 998244353)) (PreH8 : (PowmodState b_pre e_pre b e r )),
  (r = (pow_mod (b_pre) (e_pre)))
.

(*----- Function pool_sum -----*)

Definition pool_sum_safety_wit_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000000000000)) (PreH3 : (0 <= S_pre)) (PreH4 : (S_pre < 998244353)) (PreH5 : (0 <= S2_pre)) (PreH6 : (S2_pre < 998244353)),
  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pool_sum_safety_wit_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre < 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pool_sum_safety_wit_3 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition pool_sum_safety_wit_4 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 )) ”
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 )) ”
).

Definition pool_sum_safety_wit_4_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
.

Definition pool_sum_safety_wit_4_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((INT64_MIN) <= ((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 )) ”
.

Definition pool_sum_safety_wit_5 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((((S_pre * S_pre ) - S2_pre ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition pool_sum_safety_wit_6 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((S_pre * S_pre ) - S2_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((S_pre * S_pre ) - S2_pre )) ”
.

Definition pool_sum_safety_wit_7 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((S_pre * S_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (S_pre * S_pre )) ”
.

Definition pool_sum_safety_wit_8 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_safety_wit_9 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_safety_wit_10 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "cross" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_safety_wit_11 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "p2" ) )) # Int64  |->_)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((k_pre - 2 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (k_pre - 2 )) ”
.

Definition pool_sum_safety_wit_12 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "p2" ) )) # Int64  |->_)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pool_sum_safety_wit_13 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "p2" ) )) # Int64  |->_)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pool_sum_safety_wit_14 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition pool_sum_safety_wit_15 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) )) ”
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) )) ”
).

Definition pool_sum_safety_wit_15_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) <= INT64_MAX) ”
.

Definition pool_sum_safety_wit_15_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((INT64_MIN) <= ((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) )) ”
.

Definition pool_sum_safety_wit_16 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((k_pre - 1 ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition pool_sum_safety_wit_17 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((k_pre - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (k_pre - 1 )) ”
.

Definition pool_sum_safety_wit_18 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((((S2_pre % ( 998244353 ) ) * retval ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition pool_sum_safety_wit_19 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((S2_pre % ( 998244353 ) ) * retval ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((S2_pre % ( 998244353 ) ) * retval )) ”
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((S2_pre % ( 998244353 ) ) * retval ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((S2_pre % ( 998244353 ) ) * retval )) ”
).

Definition pool_sum_safety_wit_19_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((S2_pre % ( 998244353 ) ) * retval ) <= INT64_MAX) ”
.

Definition pool_sum_safety_wit_19_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((INT64_MIN) <= ((S2_pre % ( 998244353 ) ) * retval )) ”
.

Definition pool_sum_safety_wit_20 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((S2_pre <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition pool_sum_safety_wit_21 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_safety_wit_22 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_safety_wit_23 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pool_sum_safety_wit_24 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_safety_wit_25 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_safety_wit_26 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 2)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000000000000)) (PreH7 : (0 <= S_pre)) (PreH8 : (S_pre < 998244353)) (PreH9 : (0 <= S2_pre)) (PreH10 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition pool_sum_safety_wit_27 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition pool_sum_safety_wit_28 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) )) ”
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) )) ”
).

Definition pool_sum_safety_wit_28_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) <= INT64_MAX) ”
.

Definition pool_sum_safety_wit_28_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((INT64_MIN) <= (retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) )) ”
.

Definition pool_sum_safety_wit_29 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval_2 = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval_2 ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval_2)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((retval * ((k_pre - 2 ) % ( 998244353 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (retval * ((k_pre - 2 ) % ( 998244353 ) ) )) ”
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval_2 = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval_2 ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval_2)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((retval * ((k_pre - 2 ) % ( 998244353 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (retval * ((k_pre - 2 ) % ( 998244353 ) ) )) ”
).

Definition pool_sum_safety_wit_29_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval_2 = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval_2 ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval_2)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((retval * ((k_pre - 2 ) % ( 998244353 ) ) ) <= INT64_MAX) ”
.

Definition pool_sum_safety_wit_29_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval_2 = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval_2 ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval_2)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((INT64_MIN) <= (retval * ((k_pre - 2 ) % ( 998244353 ) ) )) ”
.

Definition pool_sum_safety_wit_30 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((k_pre - 2 ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition pool_sum_safety_wit_31 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((k_pre - 2 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (k_pre - 2 )) ”
.

Definition pool_sum_safety_wit_32 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre >= 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((k_pre - 3 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (k_pre - 3 )) ”
.

Definition pool_sum_safety_wit_33 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre >= 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pool_sum_safety_wit_34 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre >= 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition pool_sum_safety_wit_35 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pool_sum_safety_wit_36 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_safety_wit_37 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_safety_wit_38 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition pool_sum_safety_wit_39 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) )) ”
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) )) ”
).

Definition pool_sum_safety_wit_39_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) <= INT64_MAX) ”
.

Definition pool_sum_safety_wit_39_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((INT64_MIN) <= ((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) )) ”
.

Definition pool_sum_safety_wit_40 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) )) ”
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) )) ”
).

Definition pool_sum_safety_wit_40_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) <= INT64_MAX) ”
.

Definition pool_sum_safety_wit_40_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((INT64_MIN) <= ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) )) ”
.

Definition pool_sum_safety_wit_41 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_safety_wit_42 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition pool_sum_safety_wit_43 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) )) ”
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) )) ”
).

Definition pool_sum_safety_wit_43_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) <= INT64_MAX) ”
.

Definition pool_sum_safety_wit_43_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((INT64_MIN) <= ((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) )) ”
.

Definition pool_sum_safety_wit_44 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval )) ”
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval )) ”
).

Definition pool_sum_safety_wit_44_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) <= INT64_MAX) ”
.

Definition pool_sum_safety_wit_44_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ ((INT64_MIN) <= ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval )) ”
.

Definition pool_sum_safety_wit_45 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition pool_sum_return_wit_1 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  TT && emp 
|--
  “ ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) = (pool_closed_form (k_pre) (S_pre) (S2_pre))) ”
  &&  “ (0 <= (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) % ( 998244353 ) )) ”
  &&  “ ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) < 998244353) ”
  &&  emp
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  TT && emp 
|--
  “ ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) % ( 998244353 ) )) ”
  &&  “ ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) = (pool_closed_form (k_pre) (S_pre) (S2_pre))) ”
  &&  emp
).

Definition pool_sum_return_wit_1_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) < 998244353)
.

Definition pool_sum_return_wit_1_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  (0 <= (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) % ( 998244353 ) ))
.

Definition pool_sum_return_wit_1_split_goal_3 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (pow_mod (2) ((k_pre - 3 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 998244353)) (PreH4 : (k_pre >= 3)) (PreH5 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 998244353)) (PreH8 : (k_pre >= 2)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000000000000)) (PreH11 : (0 <= S_pre)) (PreH12 : (S_pre < 998244353)) (PreH13 : (0 <= S2_pre)) (PreH14 : (S2_pre < 998244353)),
  ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * ((retval + (retval_2 * ((k_pre - 2 ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) ) ) % ( 998244353 ) ) = (pool_closed_form (k_pre) (S_pre) (S2_pre)))
.

Definition pool_sum_return_wit_2 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  TT && emp 
|--
  “ ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) % ( 998244353 ) ) = (pool_closed_form (k_pre) (S_pre) (S2_pre))) ”
  &&  “ (0 <= (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) % ( 998244353 ) )) ”
  &&  “ ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) % ( 998244353 ) ) < 998244353) ”
  &&  emp
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  TT && emp 
|--
  “ ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) % ( 998244353 ) )) ”
  &&  “ ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) % ( 998244353 ) ) = (pool_closed_form (k_pre) (S_pre) (S2_pre))) ”
  &&  emp
).

Definition pool_sum_return_wit_2_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) % ( 998244353 ) ) < 998244353)
.

Definition pool_sum_return_wit_2_split_goal_2 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  (0 <= (((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) % ( 998244353 ) ))
.

Definition pool_sum_return_wit_2_split_goal_3 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre < 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((((((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ) + ((((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ) * retval ) ) % ( 998244353 ) ) = (pool_closed_form (k_pre) (S_pre) (S2_pre)))
.

Definition pool_sum_return_wit_3 :=
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre < 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  TT && emp 
|--
  “ (0 = (pool_closed_form (k_pre) (S_pre) (S2_pre))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < 998244353) ”
  &&  emp
) \/
(
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre < 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  TT && emp 
|--
  “ (0 = (pool_closed_form (k_pre) (S_pre) (S2_pre))) ”
  &&  emp
).

Definition pool_sum_return_wit_3_split_goal_1 :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre < 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  (0 = (pool_closed_form (k_pre) (S_pre) (S2_pre)))
.

Definition pool_sum_partial_solve_wit_1_pure :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  ((( &( "p2" ) )) # Int64  |->_)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (0 <= 2) ”
  &&  “ (2 < 998244353) ”
  &&  “ (0 <= (k_pre - 2 )) ”
  &&  “ ((k_pre - 2 ) <= 100000000000000) ”
.

Definition pool_sum_partial_solve_wit_1_aux :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (PreH1 : (k_pre >= 2)) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000000000000)) (PreH4 : (0 <= S_pre)) (PreH5 : (S_pre < 998244353)) (PreH6 : (0 <= S2_pre)) (PreH7 : (S2_pre < 998244353)),
  TT && emp 
|--
  “ (0 <= 2) ”
  &&  “ (2 < 998244353) ”
  &&  “ (0 <= (k_pre - 2 )) ”
  &&  “ ((k_pre - 2 ) <= 100000000000000) ”
  &&  “ (k_pre >= 2) ”
  &&  “ (0 <= k_pre) ”
  &&  “ (k_pre <= 100000000000000) ”
  &&  “ (0 <= S_pre) ”
  &&  “ (S_pre < 998244353) ”
  &&  “ (0 <= S2_pre) ”
  &&  “ (S2_pre < 998244353) ”
  &&  emp
.

Definition pool_sum_partial_solve_wit_1 := pool_sum_partial_solve_wit_1_pure -> pool_sum_partial_solve_wit_1_aux.

Definition pool_sum_partial_solve_wit_2_pure :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre >= 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "total" ) )) # Int64  |-> (((((S2_pre % ( 998244353 ) ) * retval ) % ( 998244353 ) ) * ((k_pre - 1 ) % ( 998244353 ) ) ) % ( 998244353 ) ))
  **  ((( &( "p2" ) )) # Int64  |-> retval)
  **  ((( &( "cross" ) )) # Int64  |-> (((((S_pre * S_pre ) - S2_pre ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "S" ) )) # Int64  |-> S_pre)
  **  ((( &( "S2" ) )) # Int64  |-> S2_pre)
|--
  “ (0 <= 2) ”
  &&  “ (2 < 998244353) ”
  &&  “ (0 <= (k_pre - 3 )) ”
  &&  “ ((k_pre - 3 ) <= 100000000000000) ”
.

Definition pool_sum_partial_solve_wit_2_aux :=
forall (k_pre: Z) (S_pre: Z) (S2_pre: Z) (retval: Z) (PreH1 : (k_pre >= 3)) (PreH2 : (retval = (pow_mod (2) ((k_pre - 2 ))))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 998244353)) (PreH5 : (k_pre >= 2)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= 100000000000000)) (PreH8 : (0 <= S_pre)) (PreH9 : (S_pre < 998244353)) (PreH10 : (0 <= S2_pre)) (PreH11 : (S2_pre < 998244353)),
  TT && emp 
|--
  “ (0 <= 2) ”
  &&  “ (2 < 998244353) ”
  &&  “ (0 <= (k_pre - 3 )) ”
  &&  “ ((k_pre - 3 ) <= 100000000000000) ”
  &&  “ (k_pre >= 3) ”
  &&  “ (retval = (pow_mod (2) ((k_pre - 2 )))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 998244353) ”
  &&  “ (k_pre >= 2) ”
  &&  “ (0 <= k_pre) ”
  &&  “ (k_pre <= 100000000000000) ”
  &&  “ (0 <= S_pre) ”
  &&  “ (S_pre < 998244353) ”
  &&  “ (0 <= S2_pre) ”
  &&  “ (S2_pre < 998244353) ”
  &&  emp
.

Definition pool_sum_partial_solve_wit_2 := pool_sum_partial_solve_wit_2_pure -> pool_sum_partial_solve_wit_2_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (d: Z) (PreH1 : (Pre vals freq )) (PreH2 : (1 <= (Zlength (vals)))) (PreH3 : ((Zlength (vals)) <= 100000)) (PreH4 : ((Zlength (freq)) = (Zlength (vals)))) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH7 : (maxv_pre = (maximum_value (vals)))) (PreH8 : (1 <= maxv_pre)) (PreH9 : (maxv_pre <= 100000)) (PreH10 : (0 <= d)) (PreH11 : (d <= maxv_pre)) (PreH12 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH13 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH14 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH15 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH16 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (d: Z) (PreH1 : (d >= 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH14 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH15 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH16 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  ((( &( "S2" ) )) # Int64  |->_)
  **  ((( &( "S" ) )) # Int64  |-> 0)
  **  ((( &( "k" ) )) # Int64  |-> 0)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (d: Z) (PreH1 : (d >= 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH14 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH15 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH16 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  ((( &( "S" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> 0)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (d: Z) (PreH1 : (d >= 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH14 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH15 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH16 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  ((( &( "k" ) )) # Int64  |->_)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ ((k + (Znth v cnts 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (k + (Znth v cnts 0) )) ”
.

Definition solver_safety_wit_6 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "k" ) )) # Int64  |-> (k + (Znth v cnts 0) ))
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (((S + (Znth v sums 0) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_7 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "k" ) )) # Int64  |-> (k + (Znth v cnts 0) ))
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ ((S + (Znth v sums 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (S + (Znth v sums 0) )) ”
.

Definition solver_safety_wit_8 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "k" ) )) # Int64  |-> (k + (Znth v cnts 0) ))
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_9 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "k" ) )) # Int64  |-> (k + (Znth v cnts 0) ))
  **  ((( &( "S" ) )) # Int64  |-> ((S + (Znth v sums 0) ) % ( 998244353 ) ))
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (((S2 + (Znth v squares 0) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_10 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "k" ) )) # Int64  |-> (k + (Znth v cnts 0) ))
  **  ((( &( "S" ) )) # Int64  |-> ((S + (Znth v sums 0) ) % ( 998244353 ) ))
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ ((S2 + (Znth v squares 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (S2 + (Znth v squares 0) )) ”
.

Definition solver_safety_wit_11 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "k" ) )) # Int64  |-> (k + (Znth v cnts 0) ))
  **  ((( &( "S" ) )) # Int64  |-> ((S + (Znth v sums 0) ) % ( 998244353 ) ))
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_12 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "k" ) )) # Int64  |-> (k + (Znth v cnts 0) ))
  **  ((( &( "S" ) )) # Int64  |-> ((S + (Znth v sums 0) ) % ( 998244353 ) ))
  **  ((( &( "S2" ) )) # Int64  |-> ((S2 + (Znth v squares 0) ) % ( 998244353 ) ))
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ ((v + d ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (v + d )) ”
.

Definition solver_safety_wit_13 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (anslist: (@list Z)) (d: Z) (cur: Z) (k: Z) (S: Z) (S2: Z) (PreH1 : (Pre vals freq )) (PreH2 : (1 <= (Zlength (vals)))) (PreH3 : ((Zlength (vals)) <= 100000)) (PreH4 : ((Zlength (freq)) = (Zlength (vals)))) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH7 : (maxv_pre = (maximum_value (vals)))) (PreH8 : (1 <= maxv_pre)) (PreH9 : (maxv_pre <= 100000)) (PreH10 : (1 <= d)) (PreH11 : (d <= maxv_pre)) (PreH12 : (0 <= cur)) (PreH13 : (cur < 998244353)) (PreH14 : (0 <= k)) (PreH15 : (k <= 100000000000000)) (PreH16 : (0 <= S)) (PreH17 : (S < 998244353)) (PreH18 : (0 <= S2)) (PreH19 : (S2 < 998244353)) (PreH20 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH21 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH22 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH23 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH24 : (PeelState vals freq d 1 cur )) (PreH25 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ ((2 * d ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * d )) ”
.

Definition solver_safety_wit_14 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (anslist: (@list Z)) (d: Z) (cur: Z) (k: Z) (S: Z) (S2: Z) (PreH1 : (Pre vals freq )) (PreH2 : (1 <= (Zlength (vals)))) (PreH3 : ((Zlength (vals)) <= 100000)) (PreH4 : ((Zlength (freq)) = (Zlength (vals)))) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH7 : (maxv_pre = (maximum_value (vals)))) (PreH8 : (1 <= maxv_pre)) (PreH9 : (maxv_pre <= 100000)) (PreH10 : (1 <= d)) (PreH11 : (d <= maxv_pre)) (PreH12 : (0 <= cur)) (PreH13 : (cur < 998244353)) (PreH14 : (0 <= k)) (PreH15 : (k <= 100000000000000)) (PreH16 : (0 <= S)) (PreH17 : (S < 998244353)) (PreH18 : (0 <= S2)) (PreH19 : (S2 < 998244353)) (PreH20 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH21 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH22 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH23 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH24 : (PeelState vals freq d 1 cur )) (PreH25 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_15 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> (((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) + 998244353 ) % ( 998244353 ) ))
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ ((v + d ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (v + d )) ”
.

Definition solver_safety_wit_16 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ ((((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) + 998244353 ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_17 :=
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ (((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) + 998244353 )) ”
) \/
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ (((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) + 998244353 )) ”
).

Definition solver_safety_wit_17_split_goal_1 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ (((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) + 998244353 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_17_split_goal_2 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ ((INT64_MIN) <= ((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) + 998244353 )) ”
.

Definition solver_safety_wit_18 :=
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ ((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (cur - ((Znth v anslist 0) % ( 998244353 ) ) )) ”
) \/
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ ((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (cur - ((Znth v anslist 0) % ( 998244353 ) ) )) ”
).

Definition solver_safety_wit_18_split_goal_1 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ ((cur - ((Znth v anslist 0) % ( 998244353 ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_18_split_goal_2 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ ((INT64_MIN) <= (cur - ((Znth v anslist 0) % ( 998244353 ) ) )) ”
.

Definition solver_safety_wit_19 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ (((Znth v anslist 0) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_20 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_21 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_22 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_23 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) (replace_Znth (d) (cur) (anslist)) )
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
|--
  “ ((d - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (d - 1 )) ”
.

Definition solver_safety_wit_24 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (d: Z) (PreH1 : (d < 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH14 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH15 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH16 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (PreH1 : (Pre vals freq )) (PreH2 : (1 <= (Zlength (vals)))) (PreH3 : ((Zlength (vals)) <= 100000)) (PreH4 : ((Zlength (freq)) = (Zlength (vals)))) (PreH5 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH6 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH7 : (maxv_pre = (maximum_value (vals)))) (PreH8 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts_2 )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums_2 )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares_2 )
  **  (Int64Array.full_shape ans_pre (maxv_pre + 1 ) )
|--
  EX (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)),
  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (0 <= maxv_pre) ”
  &&  “ (maxv_pre <= maxv_pre) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((maxv_pre < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist maxv_pre ) ”
  &&  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
) \/
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (ans_pre: Z) (maxv_pre: Z) (PreH1 : (Pre vals freq )) (PreH2 : (1 <= (Zlength (vals)))) (PreH3 : ((Zlength (vals)) <= 100000)) (PreH4 : ((Zlength (freq)) = (Zlength (vals)))) (PreH5 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH6 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH7 : (maxv_pre = (maximum_value (vals)))) (PreH8 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )),
  (Int64Array.full_shape ans_pre (maxv_pre + 1 ) )
|--
  EX (anslist: (@list Z)),
  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (0 <= maxv_pre) ”
  &&  “ (maxv_pre <= maxv_pre) ”
  &&  “ (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((maxv_pre < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist maxv_pre ) ”
  &&  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
).

Definition solver_entail_wit_2 :=
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (d: Z) (PreH1 : (d >= 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH7 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH14 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH15 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH16 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts_2 )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums_2 )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares_2 )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist_2 )
|--
  EX (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (t: Z),
  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (1 <= t) ”
  &&  “ (d = (t * d )) ”
  &&  “ (d <= d) ”
  &&  “ (d <= (maxv_pre + d )) ”
  &&  “ (((t - 1 ) * d ) <= maxv_pre) ”
  &&  “ ((t - 1 ) <= 100000) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((t - 1 ) * 1000000000 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < 998244353) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PoolAggregate cnts sums squares d (t - 1 ) 0 0 0 ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
) \/
(
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (d: Z) (PreH1 : (d >= 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH7 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH14 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH15 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH16 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  TT && emp 
|--
  EX (t: Z),
  “ (1 <= d) ”
  &&  “ (1 <= t) ”
  &&  “ (d = (t * d )) ”
  &&  “ (d <= d) ”
  &&  “ (d <= ((maximum_value (vals)) + d )) ”
  &&  “ (((t - 1 ) * d ) <= (maximum_value (vals))) ”
  &&  “ ((t - 1 ) <= 100000) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((t - 1 ) * 1000000000 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < 998244353) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < 998244353) ”
  &&  “ (PoolAggregate cnts_2 sums_2 squares_2 d (t - 1 ) 0 0 0 ) ”
  &&  emp
).

Definition solver_entail_wit_3 :=
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t_2: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t_2)) (PreH14 : (v = (t_2 * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t_2 - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t_2 - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t_2 - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist_2 0)) /\ ((Znth w_2 anslist_2 0) < 998244353)))) (PreH29 : (PoolAggregate cnts_2 sums_2 squares_2 d (t_2 - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares_2 )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums_2 )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts_2 )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist_2 )
|--
  EX (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (t: Z),
  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (1 <= t) ”
  &&  “ ((v + d ) = (t * d )) ”
  &&  “ (d <= (v + d )) ”
  &&  “ ((v + d ) <= (maxv_pre + d )) ”
  &&  “ (((t - 1 ) * d ) <= maxv_pre) ”
  &&  “ ((t - 1 ) <= 100000) ”
  &&  “ (0 <= (k + (Znth v cnts_2 0) )) ”
  &&  “ ((k + (Znth v cnts_2 0) ) <= ((t - 1 ) * 1000000000 )) ”
  &&  “ (0 <= ((S + (Znth v sums_2 0) ) % ( 998244353 ) )) ”
  &&  “ (((S + (Znth v sums_2 0) ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= ((S2 + (Znth v squares_2 0) ) % ( 998244353 ) )) ”
  &&  “ (((S2 + (Znth v squares_2 0) ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PoolAggregate cnts sums squares d (t - 1 ) (k + (Znth v cnts_2 0) ) ((S + (Znth v sums_2 0) ) % ( 998244353 ) ) ((S2 + (Znth v squares_2 0) ) % ( 998244353 ) ) ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
) \/
(
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t_2: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t_2)) (PreH14 : (v = (t_2 * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t_2 - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t_2 - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t_2 - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist_2 0)) /\ ((Znth w_2 anslist_2 0) < 998244353)))) (PreH29 : (PoolAggregate cnts_2 sums_2 squares_2 d (t_2 - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  TT && emp 
|--
  EX (t: Z),
  “ (1 <= t) ”
  &&  “ (((t_2 * d ) + d ) = (t * d )) ”
  &&  “ (d <= ((t_2 * d ) + d )) ”
  &&  “ (((t_2 * d ) + d ) <= ((maximum_value (vals)) + d )) ”
  &&  “ (((t - 1 ) * d ) <= (maximum_value (vals))) ”
  &&  “ ((t - 1 ) <= 100000) ”
  &&  “ (0 <= (k + (Znth (t_2 * d ) cnts_2 0) )) ”
  &&  “ ((k + (Znth (t_2 * d ) cnts_2 0) ) <= ((t - 1 ) * 1000000000 )) ”
  &&  “ (0 <= ((S + (Znth (t_2 * d ) sums_2 0) ) % ( 998244353 ) )) ”
  &&  “ (((S + (Znth (t_2 * d ) sums_2 0) ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= ((S2 + (Znth (t_2 * d ) squares_2 0) ) % ( 998244353 ) )) ”
  &&  “ (((S2 + (Znth (t_2 * d ) squares_2 0) ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (PoolAggregate cnts_2 sums_2 squares_2 d (t - 1 ) (k + (Znth (t_2 * d ) cnts_2 0) ) ((S + (Znth (t_2 * d ) sums_2 0) ) % ( 998244353 ) ) ((S2 + (Znth (t_2 * d ) squares_2 0) ) % ( 998244353 ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_4 :=
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (retval: Z) (PreH1 : (retval = (pool_closed_form (k) (S) (S2)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (v > maxv_pre)) (PreH5 : (Pre vals freq )) (PreH6 : (1 <= (Zlength (vals)))) (PreH7 : ((Zlength (vals)) <= 100000)) (PreH8 : ((Zlength (freq)) = (Zlength (vals)))) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH10 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH11 : (maxv_pre = (maximum_value (vals)))) (PreH12 : (1 <= maxv_pre)) (PreH13 : (maxv_pre <= 100000)) (PreH14 : (1 <= d)) (PreH15 : (d <= maxv_pre)) (PreH16 : (1 <= t)) (PreH17 : (v = (t * d ))) (PreH18 : (d <= v)) (PreH19 : (v <= (maxv_pre + d ))) (PreH20 : (((t - 1 ) * d ) <= maxv_pre)) (PreH21 : ((t - 1 ) <= 100000)) (PreH22 : (0 <= k)) (PreH23 : (k <= ((t - 1 ) * 1000000000 ))) (PreH24 : (0 <= S)) (PreH25 : (S < 998244353)) (PreH26 : (0 <= S2)) (PreH27 : (S2 < 998244353)) (PreH28 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH29 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH30 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH31 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH32 : (PoolAggregate cnts_2 sums_2 squares_2 d (t - 1 ) k S S2 )) (PreH33 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts_2 )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums_2 )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares_2 )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist_2 )
|--
  EX (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)),
  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 998244353) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= 100000000000000) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PeelState vals freq d 1 retval ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
) \/
(
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (retval: Z) (PreH1 : (retval = (pool_closed_form (k) (S) (S2)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (v > maxv_pre)) (PreH5 : (Pre vals freq )) (PreH6 : (1 <= (Zlength (vals)))) (PreH7 : ((Zlength (vals)) <= 100000)) (PreH8 : ((Zlength (freq)) = (Zlength (vals)))) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH10 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH11 : (maxv_pre = (maximum_value (vals)))) (PreH12 : (1 <= maxv_pre)) (PreH13 : (maxv_pre <= 100000)) (PreH14 : (1 <= d)) (PreH15 : (d <= maxv_pre)) (PreH16 : (1 <= t)) (PreH17 : (v = (t * d ))) (PreH18 : (d <= v)) (PreH19 : (v <= (maxv_pre + d ))) (PreH20 : (((t - 1 ) * d ) <= maxv_pre)) (PreH21 : ((t - 1 ) <= 100000)) (PreH22 : (0 <= k)) (PreH23 : (k <= ((t - 1 ) * 1000000000 ))) (PreH24 : (0 <= S)) (PreH25 : (S < 998244353)) (PreH26 : (0 <= S2)) (PreH27 : (S2 < 998244353)) (PreH28 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH29 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH30 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH31 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH32 : (PoolAggregate cnts_2 sums_2 squares_2 d (t - 1 ) k S S2 )) (PreH33 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  TT && emp 
|--
  “ (PeelState vals freq d 1 retval ) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist_2 0)) /\ ((Znth w_2 anslist_2 0) < 998244353))) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (retval: Z) (PreH1 : (retval = (pool_closed_form (k) (S) (S2)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (v > maxv_pre)) (PreH5 : (Pre vals freq )) (PreH6 : (1 <= (Zlength (vals)))) (PreH7 : ((Zlength (vals)) <= 100000)) (PreH8 : ((Zlength (freq)) = (Zlength (vals)))) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH10 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH11 : (maxv_pre = (maximum_value (vals)))) (PreH12 : (1 <= maxv_pre)) (PreH13 : (maxv_pre <= 100000)) (PreH14 : (1 <= d)) (PreH15 : (d <= maxv_pre)) (PreH16 : (1 <= t)) (PreH17 : (v = (t * d ))) (PreH18 : (d <= v)) (PreH19 : (v <= (maxv_pre + d ))) (PreH20 : (((t - 1 ) * d ) <= maxv_pre)) (PreH21 : ((t - 1 ) <= 100000)) (PreH22 : (0 <= k)) (PreH23 : (k <= ((t - 1 ) * 1000000000 ))) (PreH24 : (0 <= S)) (PreH25 : (S < 998244353)) (PreH26 : (0 <= S2)) (PreH27 : (S2 < 998244353)) (PreH28 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH29 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH30 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH31 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH32 : (PoolAggregate cnts_2 sums_2 squares_2 d (t - 1 ) k S S2 )) (PreH33 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  (PeelState vals freq d 1 retval )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (retval: Z) (PreH1 : (retval = (pool_closed_form (k) (S) (S2)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (v > maxv_pre)) (PreH5 : (Pre vals freq )) (PreH6 : (1 <= (Zlength (vals)))) (PreH7 : ((Zlength (vals)) <= 100000)) (PreH8 : ((Zlength (freq)) = (Zlength (vals)))) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH10 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH11 : (maxv_pre = (maximum_value (vals)))) (PreH12 : (1 <= maxv_pre)) (PreH13 : (maxv_pre <= 100000)) (PreH14 : (1 <= d)) (PreH15 : (d <= maxv_pre)) (PreH16 : (1 <= t)) (PreH17 : (v = (t * d ))) (PreH18 : (d <= v)) (PreH19 : (v <= (maxv_pre + d ))) (PreH20 : (((t - 1 ) * d ) <= maxv_pre)) (PreH21 : ((t - 1 ) <= 100000)) (PreH22 : (0 <= k)) (PreH23 : (k <= ((t - 1 ) * 1000000000 ))) (PreH24 : (0 <= S)) (PreH25 : (S < 998244353)) (PreH26 : (0 <= S2)) (PreH27 : (S2 < 998244353)) (PreH28 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH29 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH30 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH31 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH32 : (PoolAggregate cnts_2 sums_2 squares_2 d (t - 1 ) k S S2 )) (PreH33 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist_2 0)) /\ ((Znth w_2 anslist_2 0) < 998244353)))
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (retval: Z) (PreH1 : (retval = (pool_closed_form (k) (S) (S2)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (v > maxv_pre)) (PreH5 : (Pre vals freq )) (PreH6 : (1 <= (Zlength (vals)))) (PreH7 : ((Zlength (vals)) <= 100000)) (PreH8 : ((Zlength (freq)) = (Zlength (vals)))) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH10 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH11 : (maxv_pre = (maximum_value (vals)))) (PreH12 : (1 <= maxv_pre)) (PreH13 : (maxv_pre <= 100000)) (PreH14 : (1 <= d)) (PreH15 : (d <= maxv_pre)) (PreH16 : (1 <= t)) (PreH17 : (v = (t * d ))) (PreH18 : (d <= v)) (PreH19 : (v <= (maxv_pre + d ))) (PreH20 : (((t - 1 ) * d ) <= maxv_pre)) (PreH21 : ((t - 1 ) <= 100000)) (PreH22 : (0 <= k)) (PreH23 : (k <= ((t - 1 ) * 1000000000 ))) (PreH24 : (0 <= S)) (PreH25 : (S < 998244353)) (PreH26 : (0 <= S2)) (PreH27 : (S2 < 998244353)) (PreH28 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH29 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH30 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH31 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH32 : (PoolAggregate cnts_2 sums_2 squares_2 d (t - 1 ) k S S2 )) (PreH33 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353)))
.

Definition solver_entail_wit_4_split_goal_4 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (retval: Z) (PreH1 : (retval = (pool_closed_form (k) (S) (S2)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (v > maxv_pre)) (PreH5 : (Pre vals freq )) (PreH6 : (1 <= (Zlength (vals)))) (PreH7 : ((Zlength (vals)) <= 100000)) (PreH8 : ((Zlength (freq)) = (Zlength (vals)))) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH10 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH11 : (maxv_pre = (maximum_value (vals)))) (PreH12 : (1 <= maxv_pre)) (PreH13 : (maxv_pre <= 100000)) (PreH14 : (1 <= d)) (PreH15 : (d <= maxv_pre)) (PreH16 : (1 <= t)) (PreH17 : (v = (t * d ))) (PreH18 : (d <= v)) (PreH19 : (v <= (maxv_pre + d ))) (PreH20 : (((t - 1 ) * d ) <= maxv_pre)) (PreH21 : ((t - 1 ) <= 100000)) (PreH22 : (0 <= k)) (PreH23 : (k <= ((t - 1 ) * 1000000000 ))) (PreH24 : (0 <= S)) (PreH25 : (S < 998244353)) (PreH26 : (0 <= S2)) (PreH27 : (S2 < 998244353)) (PreH28 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH29 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH30 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH31 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH32 : (PoolAggregate cnts_2 sums_2 squares_2 d (t - 1 ) k S S2 )) (PreH33 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))
.

Definition solver_entail_wit_4_split_goal_5 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (retval: Z) (PreH1 : (retval = (pool_closed_form (k) (S) (S2)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244353)) (PreH4 : (v > maxv_pre)) (PreH5 : (Pre vals freq )) (PreH6 : (1 <= (Zlength (vals)))) (PreH7 : ((Zlength (vals)) <= 100000)) (PreH8 : ((Zlength (freq)) = (Zlength (vals)))) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH10 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH11 : (maxv_pre = (maximum_value (vals)))) (PreH12 : (1 <= maxv_pre)) (PreH13 : (maxv_pre <= 100000)) (PreH14 : (1 <= d)) (PreH15 : (d <= maxv_pre)) (PreH16 : (1 <= t)) (PreH17 : (v = (t * d ))) (PreH18 : (d <= v)) (PreH19 : (v <= (maxv_pre + d ))) (PreH20 : (((t - 1 ) * d ) <= maxv_pre)) (PreH21 : ((t - 1 ) <= 100000)) (PreH22 : (0 <= k)) (PreH23 : (k <= ((t - 1 ) * 1000000000 ))) (PreH24 : (0 <= S)) (PreH25 : (S < 998244353)) (PreH26 : (0 <= S2)) (PreH27 : (S2 < 998244353)) (PreH28 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH29 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH30 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH31 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH32 : (PoolAggregate cnts_2 sums_2 squares_2 d (t - 1 ) k S S2 )) (PreH33 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))
.

Definition solver_entail_wit_5 :=
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (anslist_2: (@list Z)) (d: Z) (cur: Z) (k: Z) (S: Z) (S2: Z) (PreH1 : (Pre vals freq )) (PreH2 : (1 <= (Zlength (vals)))) (PreH3 : ((Zlength (vals)) <= 100000)) (PreH4 : ((Zlength (freq)) = (Zlength (vals)))) (PreH5 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH6 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH7 : (maxv_pre = (maximum_value (vals)))) (PreH8 : (1 <= maxv_pre)) (PreH9 : (maxv_pre <= 100000)) (PreH10 : (1 <= d)) (PreH11 : (d <= maxv_pre)) (PreH12 : (0 <= cur)) (PreH13 : (cur < 998244353)) (PreH14 : (0 <= k)) (PreH15 : (k <= 100000000000000)) (PreH16 : (0 <= S)) (PreH17 : (S < 998244353)) (PreH18 : (0 <= S2)) (PreH19 : (S2 < 998244353)) (PreH20 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH21 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH22 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH23 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH24 : (PeelState vals freq d 1 cur )) (PreH25 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts_2 )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums_2 )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares_2 )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist_2 )
|--
  EX (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (t: Z),
  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (2 <= t) ”
  &&  “ ((2 * d ) = (t * d )) ”
  &&  “ ((2 * d ) <= (2 * d )) ”
  &&  “ ((2 * d ) <= (maxv_pre + d )) ”
  &&  “ (0 <= cur) ”
  &&  “ (cur < 998244353) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= 100000000000000) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PeelState vals freq d (t - 1 ) cur ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
) \/
(
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (anslist_2: (@list Z)) (d: Z) (cur: Z) (k: Z) (S: Z) (S2: Z) (PreH1 : (Pre vals freq )) (PreH2 : (1 <= (Zlength (vals)))) (PreH3 : ((Zlength (vals)) <= 100000)) (PreH4 : ((Zlength (freq)) = (Zlength (vals)))) (PreH5 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH6 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH7 : (maxv_pre = (maximum_value (vals)))) (PreH8 : (1 <= maxv_pre)) (PreH9 : (maxv_pre <= 100000)) (PreH10 : (1 <= d)) (PreH11 : (d <= maxv_pre)) (PreH12 : (0 <= cur)) (PreH13 : (cur < 998244353)) (PreH14 : (0 <= k)) (PreH15 : (k <= 100000000000000)) (PreH16 : (0 <= S)) (PreH17 : (S < 998244353)) (PreH18 : (0 <= S2)) (PreH19 : (S2 < 998244353)) (PreH20 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH21 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH22 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH23 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH24 : (PeelState vals freq d 1 cur )) (PreH25 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  TT && emp 
|--
  EX (t: Z),
  “ (2 <= t) ”
  &&  “ ((2 * d ) = (t * d )) ”
  &&  “ ((2 * d ) <= (2 * d )) ”
  &&  “ ((2 * d ) <= ((maximum_value (vals)) + d )) ”
  &&  “ (PeelState vals freq d (t - 1 ) cur ) ”
  &&  emp
).

Definition solver_entail_wit_6 :=
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t_2: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t_2)) (PreH14 : (v = (t_2 * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist_2 0)) /\ ((Znth w_2 anslist_2 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t_2 - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist_2 )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts_2 )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums_2 )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares_2 )
|--
  EX (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (t: Z),
  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (2 <= t) ”
  &&  “ ((v + d ) = (t * d )) ”
  &&  “ ((2 * d ) <= (v + d )) ”
  &&  “ ((v + d ) <= (maxv_pre + d )) ”
  &&  “ (0 <= (((cur - ((Znth v anslist_2 0) % ( 998244353 ) ) ) + 998244353 ) % ( 998244353 ) )) ”
  &&  “ ((((cur - ((Znth v anslist_2 0) % ( 998244353 ) ) ) + 998244353 ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= 100000000000000) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PeelState vals freq d (t - 1 ) (((cur - ((Znth v anslist_2 0) % ( 998244353 ) ) ) + 998244353 ) % ( 998244353 ) ) ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
) \/
(
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t_2: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t_2)) (PreH14 : (v = (t_2 * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist_2 0)) /\ ((Znth w_2 anslist_2 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t_2 - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  TT && emp 
|--
  EX (t: Z),
  “ (2 <= t) ”
  &&  “ (((t_2 * d ) + d ) = (t * d )) ”
  &&  “ ((2 * d ) <= ((t_2 * d ) + d )) ”
  &&  “ (((t_2 * d ) + d ) <= ((maximum_value (vals)) + d )) ”
  &&  “ (0 <= (((cur - ((Znth (t_2 * d ) anslist_2 0) % ( 998244353 ) ) ) + 998244353 ) % ( 998244353 ) )) ”
  &&  “ ((((cur - ((Znth (t_2 * d ) anslist_2 0) % ( 998244353 ) ) ) + 998244353 ) % ( 998244353 ) ) < 998244353) ”
  &&  “ (PeelState vals freq d (t - 1 ) (((cur - ((Znth (t_2 * d ) anslist_2 0) % ( 998244353 ) ) ) + 998244353 ) % ( 998244353 ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_7 :=
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH7 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH28 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) (replace_Znth (d) (cur) (anslist_2)) )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts_2 )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums_2 )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares_2 )
|--
  EX (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)),
  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (0 <= (d - 1 )) ”
  &&  “ ((d - 1 ) <= maxv_pre) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), ((((d - 1 ) < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist (d - 1 ) ) ”
  &&  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
) \/
(
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH7 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH28 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  TT && emp 
|--
  “ (AnsExactPrefix vals freq maxv_pre (replace_Znth (d) (cur) (anslist_2)) (d - 1 ) ) ”
  &&  “ forall (w_2: Z), ((((d - 1 ) < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 (replace_Znth (d) (cur) (anslist_2)) 0)) /\ ((Znth w_2 (replace_Znth (d) (cur) (anslist_2)) 0) < 998244353))) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353))) ”
  &&  “ ((Zlength ((replace_Znth (d) (cur) (anslist_2)))) = (maxv_pre + 1 )) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH7 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH28 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  (AnsExactPrefix vals freq maxv_pre (replace_Znth (d) (cur) (anslist_2)) (d - 1 ) )
.

Definition solver_entail_wit_7_split_goal_2 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH7 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH28 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  forall (w_2: Z), ((((d - 1 ) < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 (replace_Znth (d) (cur) (anslist_2)) 0)) /\ ((Znth w_2 (replace_Znth (d) (cur) (anslist_2)) 0) < 998244353)))
.

Definition solver_entail_wit_7_split_goal_3 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH7 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH28 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353)))
.

Definition solver_entail_wit_7_split_goal_4 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH7 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH28 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  ((Zlength ((replace_Znth (d) (cur) (anslist_2)))) = (maxv_pre + 1 ))
.

Definition solver_entail_wit_7_split_goal_5 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH7 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH28 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))
.

Definition solver_entail_wit_7_split_goal_6 :=
forall (freq: (@list Z)) (vals: (@list Z)) (maxv_pre: Z) (anslist_2: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < (Zlength (vals)))) -> ((1 <= (Znth i_3 vals 0)) /\ ((Znth i_3 vals 0) <= 100000)))) (PreH7 : forall (i_4: Z), (((0 <= i_4) /\ (i_4 < (Zlength (freq)))) -> ((1 <= (Znth i_4 freq 0)) /\ ((Znth i_4 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH26 : ((Zlength (anslist_2)) = (maxv_pre + 1 ))) (PreH27 : forall (w_3: Z), (((0 <= w_3) /\ (w_3 <= maxv_pre)) -> ((((((0 <= (Znth w_3 cnts_2 0)) /\ ((Znth w_3 cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w_3 sums_2 0))) /\ ((Znth w_3 sums_2 0) < 998244353)) /\ (0 <= (Znth w_3 squares_2 0))) /\ ((Znth w_3 squares_2 0) < 998244353)))) (PreH28 : forall (w_4: Z), (((d < w_4) /\ (w_4 <= maxv_pre)) -> ((0 <= (Znth w_4 anslist_2 0)) /\ ((Znth w_4 anslist_2 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist_2 d )),
  forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))
.

Definition solver_return_wit_1 :=
(
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (d: Z) (PreH1 : (d < 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH14 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH15 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353)))) (PreH16 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts_2 )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums_2 )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares_2 )
|--
  EX (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)),
  “ (Spec vals freq (Znth 1 anslist 0) ) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full_shape ans_pre (maxv_pre + 1 ) )
) \/
(
forall (freq: (@list Z)) (vals: (@list Z)) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (d: Z) (PreH1 : (d < 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH14 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH15 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353)))) (PreH16 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (Spec vals freq (Znth 1 anslist 0) ) ”
  &&  (Int64Array.full_shape ans_pre (maxv_pre + 1 ) )
).

Definition solver_return_wit_1_split_goal_1 :=
forall (freq: (@list Z)) (vals: (@list Z)) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (d: Z) (PreH1 : (d < 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH14 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH15 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353)))) (PreH16 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (Spec vals freq (Znth 1 anslist 0) ) ”
.

Definition solver_return_wit_1_split_goal_spatial :=
forall (freq: (@list Z)) (vals: (@list Z)) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts_2: (@list Z)) (sums_2: (@list Z)) (squares_2: (@list Z)) (d: Z) (PreH1 : (d < 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts_2 sums_2 squares_2 maxv_pre )) (PreH14 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH15 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts_2 0)) /\ ((Znth w cnts_2 0) <= 1000000000)) /\ (0 <= (Znth w sums_2 0))) /\ ((Znth w sums_2 0) < 998244353)) /\ (0 <= (Znth w squares_2 0))) /\ ((Znth w squares_2 0) < 998244353)))) (PreH16 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  (Int64Array.full_shape ans_pre (maxv_pre + 1 ) )
.

Definition solver_partial_solve_wit_1 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (v <= maxv_pre) ”
  &&  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (1 <= t) ”
  &&  “ (v = (t * d )) ”
  &&  “ (d <= v) ”
  &&  “ (v <= (maxv_pre + d )) ”
  &&  “ (((t - 1 ) * d ) <= maxv_pre) ”
  &&  “ ((t - 1 ) <= 100000) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= ((t - 1 ) * 1000000000 )) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PoolAggregate cnts sums squares d (t - 1 ) k S S2 ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (((cnt_pre + (v * sizeof(INT64)))) # Int64  |-> (Znth v cnts 0))
  **  (Int64Array.missing_i cnt_pre v 0 (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
.

Definition solver_partial_solve_wit_2 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (v <= maxv_pre) ”
  &&  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (1 <= t) ”
  &&  “ (v = (t * d )) ”
  &&  “ (d <= v) ”
  &&  “ (v <= (maxv_pre + d )) ”
  &&  “ (((t - 1 ) * d ) <= maxv_pre) ”
  &&  “ ((t - 1 ) <= 100000) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= ((t - 1 ) * 1000000000 )) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PoolAggregate cnts sums squares d (t - 1 ) k S S2 ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (((sum_pre + (v * sizeof(INT64)))) # Int64  |-> (Znth v sums 0))
  **  (Int64Array.missing_i sum_pre v 0 (maxv_pre + 1 ) sums )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
.

Definition solver_partial_solve_wit_3 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (v <= maxv_pre) ”
  &&  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (1 <= t) ”
  &&  “ (v = (t * d )) ”
  &&  “ (d <= v) ”
  &&  “ (v <= (maxv_pre + d )) ”
  &&  “ (((t - 1 ) * d ) <= maxv_pre) ”
  &&  “ ((t - 1 ) <= 100000) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= ((t - 1 ) * 1000000000 )) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PoolAggregate cnts sums squares d (t - 1 ) k S S2 ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (((sqsum_pre + (v * sizeof(INT64)))) # Int64  |-> (Znth v squares 0))
  **  (Int64Array.missing_i sqsum_pre v 0 (maxv_pre + 1 ) squares )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
.

Definition solver_partial_solve_wit_4_pure :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  ((( &( "cur" ) )) # Int64  |->_)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "sum" ) )) # Ptr  |-> sum_pre)
  **  ((( &( "sqsum" ) )) # Ptr  |-> sqsum_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "maxv" ) )) # Int  |-> maxv_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "S" ) )) # Int64  |-> S)
  **  ((( &( "S2" ) )) # Int64  |-> S2)
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (0 <= k) ”
  &&  “ (k <= 100000000000000) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
.

Definition solver_partial_solve_wit_4_aux :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (1 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : (d <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (((t - 1 ) * d ) <= maxv_pre)) (PreH18 : ((t - 1 ) <= 100000)) (PreH19 : (0 <= k)) (PreH20 : (k <= ((t - 1 ) * 1000000000 ))) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PoolAggregate cnts sums squares d (t - 1 ) k S S2 )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (0 <= k) ”
  &&  “ (k <= 100000000000000) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
  &&  “ (v > maxv_pre) ”
  &&  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (1 <= t) ”
  &&  “ (v = (t * d )) ”
  &&  “ (d <= v) ”
  &&  “ (v <= (maxv_pre + d )) ”
  &&  “ (((t - 1 ) * d ) <= maxv_pre) ”
  &&  “ ((t - 1 ) <= 100000) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= ((t - 1 ) * 1000000000 )) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PoolAggregate cnts sums squares d (t - 1 ) k S S2 ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v <= maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (v <= maxv_pre) ”
  &&  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (2 <= t) ”
  &&  “ (v = (t * d )) ”
  &&  “ ((2 * d ) <= v) ”
  &&  “ (v <= (maxv_pre + d )) ”
  &&  “ (0 <= cur) ”
  &&  “ (cur < 998244353) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= 100000000000000) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PeelState vals freq d (t - 1 ) cur ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (((ans_pre + (v * sizeof(INT64)))) # Int64  |-> (Znth v anslist 0))
  **  (Int64Array.missing_i ans_pre v 0 (maxv_pre + 1 ) anslist )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
.

Definition solver_partial_solve_wit_6 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (S2: Z) (S: Z) (k: Z) (cur: Z) (v: Z) (t: Z) (d: Z) (PreH1 : (v > maxv_pre)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (1 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (2 <= t)) (PreH14 : (v = (t * d ))) (PreH15 : ((2 * d ) <= v)) (PreH16 : (v <= (maxv_pre + d ))) (PreH17 : (0 <= cur)) (PreH18 : (cur < 998244353)) (PreH19 : (0 <= k)) (PreH20 : (k <= 100000000000000)) (PreH21 : (0 <= S)) (PreH22 : (S < 998244353)) (PreH23 : (0 <= S2)) (PreH24 : (S2 < 998244353)) (PreH25 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH26 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH27 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH28 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH29 : (PeelState vals freq d (t - 1 ) cur )) (PreH30 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (v > maxv_pre) ”
  &&  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (1 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (2 <= t) ”
  &&  “ (v = (t * d )) ”
  &&  “ ((2 * d ) <= v) ”
  &&  “ (v <= (maxv_pre + d )) ”
  &&  “ (0 <= cur) ”
  &&  “ (cur < 998244353) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= 100000000000000) ”
  &&  “ (0 <= S) ”
  &&  “ (S < 998244353) ”
  &&  “ (0 <= S2) ”
  &&  “ (S2 < 998244353) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (PeelState vals freq d (t - 1 ) cur ) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (((ans_pre + (d * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i ans_pre d 0 (maxv_pre + 1 ) anslist )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
.

Definition solver_partial_solve_wit_7 :=
forall (freq: (@list Z)) (vals: (@list Z)) (cnt_pre: Z) (sum_pre: Z) (sqsum_pre: Z) (ans_pre: Z) (maxv_pre: Z) (anslist: (@list Z)) (cnts: (@list Z)) (sums: (@list Z)) (squares: (@list Z)) (d: Z) (PreH1 : (d < 1)) (PreH2 : (Pre vals freq )) (PreH3 : (1 <= (Zlength (vals)))) (PreH4 : ((Zlength (vals)) <= 100000)) (PreH5 : ((Zlength (freq)) = (Zlength (vals)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000)))) (PreH8 : (maxv_pre = (maximum_value (vals)))) (PreH9 : (1 <= maxv_pre)) (PreH10 : (maxv_pre <= 100000)) (PreH11 : (0 <= d)) (PreH12 : (d <= maxv_pre)) (PreH13 : (aggregate_arrays vals freq cnts sums squares maxv_pre )) (PreH14 : ((Zlength (anslist)) = (maxv_pre + 1 ))) (PreH15 : forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353)))) (PreH16 : forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353)))) (PreH17 : (AnsExactPrefix vals freq maxv_pre anslist d )),
  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
  **  (Int64Array.full ans_pre (maxv_pre + 1 ) anslist )
|--
  “ (d < 1) ”
  &&  “ (Pre vals freq ) ”
  &&  “ (1 <= (Zlength (vals))) ”
  &&  “ ((Zlength (vals)) <= 100000) ”
  &&  “ ((Zlength (freq)) = (Zlength (vals))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (vals)))) -> ((1 <= (Znth i vals 0)) /\ ((Znth i vals 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (freq)))) -> ((1 <= (Znth i_2 freq 0)) /\ ((Znth i_2 freq 0) <= 1000000000))) ”
  &&  “ (maxv_pre = (maximum_value (vals))) ”
  &&  “ (1 <= maxv_pre) ”
  &&  “ (maxv_pre <= 100000) ”
  &&  “ (0 <= d) ”
  &&  “ (d <= maxv_pre) ”
  &&  “ (aggregate_arrays vals freq cnts sums squares maxv_pre ) ”
  &&  “ ((Zlength (anslist)) = (maxv_pre + 1 )) ”
  &&  “ forall (w: Z), (((0 <= w) /\ (w <= maxv_pre)) -> ((((((0 <= (Znth w cnts 0)) /\ ((Znth w cnts 0) <= 1000000000)) /\ (0 <= (Znth w sums 0))) /\ ((Znth w sums 0) < 998244353)) /\ (0 <= (Znth w squares 0))) /\ ((Znth w squares 0) < 998244353))) ”
  &&  “ forall (w_2: Z), (((d < w_2) /\ (w_2 <= maxv_pre)) -> ((0 <= (Znth w_2 anslist 0)) /\ ((Znth w_2 anslist 0) < 998244353))) ”
  &&  “ (AnsExactPrefix vals freq maxv_pre anslist d ) ”
  &&  (((ans_pre + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 anslist 0))
  **  (Int64Array.missing_i ans_pre 1 0 (maxv_pre + 1 ) anslist )
  **  (Int64Array.full cnt_pre (maxv_pre + 1 ) cnts )
  **  (Int64Array.full sum_pre (maxv_pre + 1 ) sums )
  **  (Int64Array.full sqsum_pre (maxv_pre + 1 ) squares )
.

Module Type VC_Correct.


Axiom proof_of_powmod_safety_wit_1 : powmod_safety_wit_1.
Axiom proof_of_powmod_safety_wit_2 : powmod_safety_wit_2.
Axiom proof_of_powmod_safety_wit_3 : powmod_safety_wit_3.
Axiom proof_of_powmod_safety_wit_4 : powmod_safety_wit_4.
Axiom proof_of_powmod_safety_wit_5 : powmod_safety_wit_5.
Axiom proof_of_powmod_safety_wit_6 : powmod_safety_wit_6.
Axiom proof_of_powmod_safety_wit_7 : powmod_safety_wit_7.
Axiom proof_of_powmod_safety_wit_8 : powmod_safety_wit_8.
Axiom proof_of_powmod_safety_wit_9 : powmod_safety_wit_9.
Axiom proof_of_powmod_safety_wit_10 : powmod_safety_wit_10.
Axiom proof_of_powmod_safety_wit_11 : powmod_safety_wit_11.
Axiom proof_of_powmod_safety_wit_12 : powmod_safety_wit_12.
Axiom proof_of_powmod_safety_wit_13 : powmod_safety_wit_13.
Axiom proof_of_powmod_safety_wit_14 : powmod_safety_wit_14.
Axiom proof_of_powmod_safety_wit_15 : powmod_safety_wit_15.
Axiom proof_of_powmod_safety_wit_16 : powmod_safety_wit_16.
Axiom proof_of_powmod_safety_wit_17 : powmod_safety_wit_17.
Axiom proof_of_powmod_safety_wit_18 : powmod_safety_wit_18.
Axiom proof_of_powmod_safety_wit_19 : powmod_safety_wit_19.
Axiom proof_of_powmod_safety_wit_20 : powmod_safety_wit_20.
Axiom proof_of_powmod_safety_wit_21 : powmod_safety_wit_21.
Axiom proof_of_powmod_entail_wit_1_1 : powmod_entail_wit_1_1.
Axiom proof_of_powmod_entail_wit_1_2 : powmod_entail_wit_1_2.
Axiom proof_of_powmod_entail_wit_2_1 : powmod_entail_wit_2_1.
Axiom proof_of_powmod_entail_wit_2_2 : powmod_entail_wit_2_2.
Axiom proof_of_powmod_return_wit_1 : powmod_return_wit_1.
Axiom proof_of_pool_sum_safety_wit_1 : pool_sum_safety_wit_1.
Axiom proof_of_pool_sum_safety_wit_2 : pool_sum_safety_wit_2.
Axiom proof_of_pool_sum_safety_wit_3 : pool_sum_safety_wit_3.
Axiom proof_of_pool_sum_safety_wit_4 : pool_sum_safety_wit_4.
Axiom proof_of_pool_sum_safety_wit_5 : pool_sum_safety_wit_5.
Axiom proof_of_pool_sum_safety_wit_6 : pool_sum_safety_wit_6.
Axiom proof_of_pool_sum_safety_wit_7 : pool_sum_safety_wit_7.
Axiom proof_of_pool_sum_safety_wit_8 : pool_sum_safety_wit_8.
Axiom proof_of_pool_sum_safety_wit_9 : pool_sum_safety_wit_9.
Axiom proof_of_pool_sum_safety_wit_10 : pool_sum_safety_wit_10.
Axiom proof_of_pool_sum_safety_wit_11 : pool_sum_safety_wit_11.
Axiom proof_of_pool_sum_safety_wit_12 : pool_sum_safety_wit_12.
Axiom proof_of_pool_sum_safety_wit_13 : pool_sum_safety_wit_13.
Axiom proof_of_pool_sum_safety_wit_14 : pool_sum_safety_wit_14.
Axiom proof_of_pool_sum_safety_wit_15 : pool_sum_safety_wit_15.
Axiom proof_of_pool_sum_safety_wit_16 : pool_sum_safety_wit_16.
Axiom proof_of_pool_sum_safety_wit_17 : pool_sum_safety_wit_17.
Axiom proof_of_pool_sum_safety_wit_18 : pool_sum_safety_wit_18.
Axiom proof_of_pool_sum_safety_wit_19 : pool_sum_safety_wit_19.
Axiom proof_of_pool_sum_safety_wit_20 : pool_sum_safety_wit_20.
Axiom proof_of_pool_sum_safety_wit_21 : pool_sum_safety_wit_21.
Axiom proof_of_pool_sum_safety_wit_22 : pool_sum_safety_wit_22.
Axiom proof_of_pool_sum_safety_wit_23 : pool_sum_safety_wit_23.
Axiom proof_of_pool_sum_safety_wit_24 : pool_sum_safety_wit_24.
Axiom proof_of_pool_sum_safety_wit_25 : pool_sum_safety_wit_25.
Axiom proof_of_pool_sum_safety_wit_26 : pool_sum_safety_wit_26.
Axiom proof_of_pool_sum_safety_wit_27 : pool_sum_safety_wit_27.
Axiom proof_of_pool_sum_safety_wit_28 : pool_sum_safety_wit_28.
Axiom proof_of_pool_sum_safety_wit_29 : pool_sum_safety_wit_29.
Axiom proof_of_pool_sum_safety_wit_30 : pool_sum_safety_wit_30.
Axiom proof_of_pool_sum_safety_wit_31 : pool_sum_safety_wit_31.
Axiom proof_of_pool_sum_safety_wit_32 : pool_sum_safety_wit_32.
Axiom proof_of_pool_sum_safety_wit_33 : pool_sum_safety_wit_33.
Axiom proof_of_pool_sum_safety_wit_34 : pool_sum_safety_wit_34.
Axiom proof_of_pool_sum_safety_wit_35 : pool_sum_safety_wit_35.
Axiom proof_of_pool_sum_safety_wit_36 : pool_sum_safety_wit_36.
Axiom proof_of_pool_sum_safety_wit_37 : pool_sum_safety_wit_37.
Axiom proof_of_pool_sum_safety_wit_38 : pool_sum_safety_wit_38.
Axiom proof_of_pool_sum_safety_wit_39 : pool_sum_safety_wit_39.
Axiom proof_of_pool_sum_safety_wit_40 : pool_sum_safety_wit_40.
Axiom proof_of_pool_sum_safety_wit_41 : pool_sum_safety_wit_41.
Axiom proof_of_pool_sum_safety_wit_42 : pool_sum_safety_wit_42.
Axiom proof_of_pool_sum_safety_wit_43 : pool_sum_safety_wit_43.
Axiom proof_of_pool_sum_safety_wit_44 : pool_sum_safety_wit_44.
Axiom proof_of_pool_sum_safety_wit_45 : pool_sum_safety_wit_45.
Axiom proof_of_pool_sum_return_wit_1 : pool_sum_return_wit_1.
Axiom proof_of_pool_sum_return_wit_2 : pool_sum_return_wit_2.
Axiom proof_of_pool_sum_return_wit_3 : pool_sum_return_wit_3.
Axiom proof_of_pool_sum_partial_solve_wit_1_pure : pool_sum_partial_solve_wit_1_pure.
Axiom proof_of_pool_sum_partial_solve_wit_1 : pool_sum_partial_solve_wit_1.
Axiom proof_of_pool_sum_partial_solve_wit_2_pure : pool_sum_partial_solve_wit_2_pure.
Axiom proof_of_pool_sum_partial_solve_wit_2 : pool_sum_partial_solve_wit_2.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
