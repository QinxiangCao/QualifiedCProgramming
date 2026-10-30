From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P033_1737B_elas_fitness_and_the_luxury_number_lib.
Local Open Scope sac.

(*----- Function isqrt -----*)

Definition isqrt_safety_wit_1 :=
forall (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= 1000000000000000000)),
  ((( &( "hi" ) )) # Int64  |->_)
  **  ((( &( "lo" ) )) # Int64  |-> 0)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
|--
  “ (2000000000 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 2000000000) ”
.

Definition isqrt_safety_wit_2 :=
forall (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= 1000000000000000000)),
  ((( &( "lo" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition isqrt_safety_wit_3 :=
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
).

Definition isqrt_safety_wit_3_split_goal_1 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX) ”
.

Definition isqrt_safety_wit_3_split_goal_2 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((INT64_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition isqrt_safety_wit_4 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((((hi - lo ) + 1 ) <> (INT64_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition isqrt_safety_wit_5 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((hi - lo ) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((hi - lo ) + 1 )) ”
.

Definition isqrt_safety_wit_6 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((hi - lo ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (hi - lo )) ”
.

Definition isqrt_safety_wit_7 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition isqrt_safety_wit_8 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition isqrt_safety_wit_9 :=
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((v_pre <> (INT64_MIN)) \/ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <> (-1))) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <> 0) ”
) \/
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((v_pre <> (INT64_MIN)) \/ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <> (-1))) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <> 0) ”
).

Definition isqrt_safety_wit_9_split_goal_1 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((v_pre <> (INT64_MIN)) \/ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <> (-1))) ”
.

Definition isqrt_safety_wit_9_split_goal_2 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <> 0) ”
.

Definition isqrt_safety_wit_10 :=
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) > (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
) \/
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) > (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
).

Definition isqrt_safety_wit_10_split_goal_1 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) > (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT64_MAX) ”
.

Definition isqrt_safety_wit_10_split_goal_2 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) > (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((INT64_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
.

Definition isqrt_safety_wit_11 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) > (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition isqrt_entail_wit_1 :=
(
forall (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (0 <= v_pre) ”
  &&  “ (v_pre <= 1000000000000000000) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 2000000000) ”
  &&  “ (2000000000 <= 2000000000) ”
  &&  “ (SqrtSearchBounds v_pre 0 2000000000 ) ”
  &&  emp
) \/
(
forall (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (SqrtSearchBounds v_pre 0 2000000000 ) ”
  &&  emp
).

Definition isqrt_entail_wit_1_split_goal_1 :=
forall (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= 1000000000000000000)),
  (SqrtSearchBounds v_pre 0 2000000000 )
.

Definition isqrt_entail_wit_2_1 :=
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  TT && emp 
|--
  “ (0 <= v_pre) ”
  &&  “ (v_pre <= 1000000000000000000) ”
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ”
  &&  “ (hi <= 2000000000) ”
  &&  “ (SqrtSearchBounds v_pre (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) hi ) ”
  &&  emp
) \/
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  TT && emp 
|--
  “ (SqrtSearchBounds v_pre (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) hi ) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ”
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  emp
).

Definition isqrt_entail_wit_2_1_split_goal_1 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  (SqrtSearchBounds v_pre (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) hi )
.

Definition isqrt_entail_wit_2_1_split_goal_2 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi)
.

Definition isqrt_entail_wit_2_1_split_goal_3 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
.

Definition isqrt_entail_wit_2_2 :=
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) > (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  TT && emp 
|--
  “ (0 <= v_pre) ”
  &&  “ (v_pre <= 1000000000000000000) ”
  &&  “ (0 <= lo) ”
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 2000000000) ”
  &&  “ (SqrtSearchBounds v_pre lo ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) ) ”
  &&  emp
) \/
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) > (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  TT && emp 
|--
  “ (SqrtSearchBounds v_pre lo ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) ) ”
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 2000000000) ”
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
  &&  emp
).

Definition isqrt_entail_wit_2_2_split_goal_1 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) > (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  (SqrtSearchBounds v_pre lo ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) )
.

Definition isqrt_entail_wit_2_2_split_goal_2 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) > (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 2000000000)
.

Definition isqrt_entail_wit_2_2_split_goal_3 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) > (v_pre ÷ (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH2 : (lo < hi)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= 1000000000000000000)) (PreH5 : (0 <= lo)) (PreH6 : (lo <= hi)) (PreH7 : (hi <= 2000000000)) (PreH8 : (SqrtSearchBounds v_pre lo hi )),
  (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ))
.

Definition isqrt_return_wit_1 :=
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  TT && emp 
|--
  “ (ISqrtSpec v_pre lo ) ”
  &&  emp
) \/
(
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  TT && emp 
|--
  “ (ISqrtSpec v_pre lo ) ”
  &&  emp
).

Definition isqrt_return_wit_1_split_goal_1 :=
forall (v_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= 1000000000000000000)) (PreH4 : (0 <= lo)) (PreH5 : (lo <= hi)) (PreH6 : (hi <= 2000000000)) (PreH7 : (SqrtSearchBounds v_pre lo hi )),
  (ISqrtSpec v_pre lo )
.

(*----- Function count_upto -----*)

Definition count_upto_safety_wit_1 :=
forall (x_pre: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)),
  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_upto_safety_wit_2 :=
forall (x_pre: Z) (PreH1 : (x_pre <= 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)),
  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_upto_safety_wit_3 :=
(
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((3 * (retval - 1 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (3 * (retval - 1 ) )) ”
) \/
(
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((3 * (retval - 1 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (3 * (retval - 1 ) )) ”
).

Definition count_upto_safety_wit_3_split_goal_1 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((3 * (retval - 1 ) ) <= INT64_MAX) ”
.

Definition count_upto_safety_wit_3_split_goal_2 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((INT64_MIN) <= (3 * (retval - 1 ) )) ”
.

Definition count_upto_safety_wit_4 :=
(
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((retval - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (retval - 1 )) ”
) \/
(
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((retval - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (retval - 1 )) ”
).

Definition count_upto_safety_wit_4_split_goal_1 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((retval - 1 ) <= INT64_MAX) ”
.

Definition count_upto_safety_wit_4_split_goal_2 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((INT64_MIN) <= (retval - 1 )) ”
.

Definition count_upto_safety_wit_5 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition count_upto_safety_wit_6 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_upto_safety_wit_7 :=
(
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "base" ) )) # Int64  |->_)
  **  ((( &( "cnt" ) )) # Int64  |-> (3 * (retval - 1 ) ))
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((retval * retval ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (retval * retval )) ”
) \/
(
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "base" ) )) # Int64  |->_)
  **  ((( &( "cnt" ) )) # Int64  |-> (3 * (retval - 1 ) ))
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((retval * retval ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (retval * retval )) ”
).

Definition count_upto_safety_wit_7_split_goal_1 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "base" ) )) # Int64  |->_)
  **  ((( &( "cnt" ) )) # Int64  |-> (3 * (retval - 1 ) ))
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((retval * retval ) <= INT64_MAX) ”
.

Definition count_upto_safety_wit_7_split_goal_2 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "base" ) )) # Int64  |->_)
  **  ((( &( "cnt" ) )) # Int64  |-> (3 * (retval - 1 ) ))
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ ((INT64_MIN) <= (retval * retval )) ”
.

Definition count_upto_safety_wit_8 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "base" ) )) # Int64  |-> (retval * retval ))
  **  ((( &( "cnt" ) )) # Int64  |-> (3 * (retval - 1 ) ))
  **  ((( &( "s" ) )) # Int64  |-> retval)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_upto_safety_wit_9 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (1 <= s)) (PreH4 : (s <= 1000000000)) (PreH5 : (ISqrtSpec x_pre s )) (PreH6 : (base = (s * s ))) (PreH7 : (0 <= m)) (PreH8 : (m <= 3)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= (3 * s ))) (PreH11 : (cnt <= 3000000000)) (PreH12 : (LuxuryBlockPrefix x_pre s m cnt )),
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "cnt" ) )) # Int64  |-> cnt)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition count_upto_safety_wit_10 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : (m < 3)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (1 <= s)) (PreH5 : (s <= 1000000000)) (PreH6 : (ISqrtSpec x_pre s )) (PreH7 : (base = (s * s ))) (PreH8 : (0 <= m)) (PreH9 : (m <= 3)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= (3 * s ))) (PreH12 : (cnt <= 3000000000)) (PreH13 : (LuxuryBlockPrefix x_pre s m cnt )),
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "cnt" ) )) # Int64  |-> cnt)
|--
  “ ((base + (m * s ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (base + (m * s ) )) ”
.

Definition count_upto_safety_wit_11 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : (m < 3)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (1 <= s)) (PreH5 : (s <= 1000000000)) (PreH6 : (ISqrtSpec x_pre s )) (PreH7 : (base = (s * s ))) (PreH8 : (0 <= m)) (PreH9 : (m <= 3)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= (3 * s ))) (PreH12 : (cnt <= 3000000000)) (PreH13 : (LuxuryBlockPrefix x_pre s m cnt )),
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "cnt" ) )) # Int64  |-> cnt)
|--
  “ ((m * s ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (m * s )) ”
.

Definition count_upto_safety_wit_12 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) <= x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "cnt" ) )) # Int64  |-> cnt)
|--
  “ ((cnt + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (cnt + 1 )) ”
.

Definition count_upto_safety_wit_13 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) <= x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "cnt" ) )) # Int64  |-> (cnt + 1 ))
|--
  “ ((m + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (m + 1 )) ”
.

Definition count_upto_safety_wit_14 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) > x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "cnt" ) )) # Int64  |-> cnt)
|--
  “ ((m + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (m + 1 )) ”
.

Definition count_upto_entail_wit_1 :=
(
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (1 <= x_pre) ”
  &&  “ (x_pre <= 1000000000000000000) ”
  &&  “ (1 <= retval) ”
  &&  “ (retval <= 1000000000) ”
  &&  “ (ISqrtSpec x_pre retval ) ”
  &&  “ ((retval * retval ) = (retval * retval )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 3) ”
  &&  “ (0 <= (3 * (retval - 1 ) )) ”
  &&  “ ((3 * (retval - 1 ) ) <= (3 * retval )) ”
  &&  “ ((3 * (retval - 1 ) ) <= 3000000000) ”
  &&  “ (LuxuryBlockPrefix x_pre retval 0 (3 * (retval - 1 ) ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (LuxuryBlockPrefix x_pre retval 0 (3 * (retval - 1 ) ) ) ”
  &&  “ ((3 * (retval - 1 ) ) <= 3000000000) ”
  &&  “ (0 <= (3 * (retval - 1 ) )) ”
  &&  “ (retval <= 1000000000) ”
  &&  “ (1 <= retval) ”
  &&  emp
).

Definition count_upto_entail_wit_1_split_goal_1 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  (LuxuryBlockPrefix x_pre retval 0 (3 * (retval - 1 ) ) )
.

Definition count_upto_entail_wit_1_split_goal_2 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  ((3 * (retval - 1 ) ) <= 3000000000)
.

Definition count_upto_entail_wit_1_split_goal_3 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  (0 <= (3 * (retval - 1 ) ))
.

Definition count_upto_entail_wit_1_split_goal_4 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  (retval <= 1000000000)
.

Definition count_upto_entail_wit_1_split_goal_5 :=
forall (x_pre: Z) (retval: Z) (PreH1 : (ISqrtSpec x_pre retval )) (PreH2 : (x_pre > 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)),
  (1 <= retval)
.

Definition count_upto_entail_wit_2_1 :=
(
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) <= x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  TT && emp 
|--
  “ (1 <= x_pre) ”
  &&  “ (x_pre <= 1000000000000000000) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= 1000000000) ”
  &&  “ (ISqrtSpec x_pre s ) ”
  &&  “ (base = (s * s )) ”
  &&  “ (0 <= (m + 1 )) ”
  &&  “ ((m + 1 ) <= 3) ”
  &&  “ (0 <= (cnt + 1 )) ”
  &&  “ ((cnt + 1 ) <= (3 * s )) ”
  &&  “ ((cnt + 1 ) <= 3000000000) ”
  &&  “ (LuxuryBlockPrefix x_pre s (m + 1 ) (cnt + 1 ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) <= x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  TT && emp 
|--
  “ (LuxuryBlockPrefix x_pre s (m + 1 ) (cnt + 1 ) ) ”
  &&  “ ((cnt + 1 ) <= 3000000000) ”
  &&  “ ((cnt + 1 ) <= (3 * s )) ”
  &&  emp
).

Definition count_upto_entail_wit_2_1_split_goal_1 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) <= x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  (LuxuryBlockPrefix x_pre s (m + 1 ) (cnt + 1 ) )
.

Definition count_upto_entail_wit_2_1_split_goal_2 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) <= x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  ((cnt + 1 ) <= 3000000000)
.

Definition count_upto_entail_wit_2_1_split_goal_3 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) <= x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  ((cnt + 1 ) <= (3 * s ))
.

Definition count_upto_entail_wit_2_2 :=
(
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) > x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  TT && emp 
|--
  “ (1 <= x_pre) ”
  &&  “ (x_pre <= 1000000000000000000) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= 1000000000) ”
  &&  “ (ISqrtSpec x_pre s ) ”
  &&  “ (base = (s * s )) ”
  &&  “ (0 <= (m + 1 )) ”
  &&  “ ((m + 1 ) <= 3) ”
  &&  “ (0 <= cnt) ”
  &&  “ (cnt <= (3 * s )) ”
  &&  “ (cnt <= 3000000000) ”
  &&  “ (LuxuryBlockPrefix x_pre s (m + 1 ) cnt ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) > x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  TT && emp 
|--
  “ (LuxuryBlockPrefix x_pre s (m + 1 ) cnt ) ”
  &&  emp
).

Definition count_upto_entail_wit_2_2_split_goal_1 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : ((base + (m * s ) ) > x_pre)) (PreH2 : (m < 3)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1000000000000000000)) (PreH5 : (1 <= s)) (PreH6 : (s <= 1000000000)) (PreH7 : (ISqrtSpec x_pre s )) (PreH8 : (base = (s * s ))) (PreH9 : (0 <= m)) (PreH10 : (m <= 3)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= (3 * s ))) (PreH13 : (cnt <= 3000000000)) (PreH14 : (LuxuryBlockPrefix x_pre s m cnt )),
  (LuxuryBlockPrefix x_pre s (m + 1 ) cnt )
.

Definition count_upto_return_wit_1 :=
(
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : (m >= 3)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (1 <= s)) (PreH5 : (s <= 1000000000)) (PreH6 : (ISqrtSpec x_pre s )) (PreH7 : (base = (s * s ))) (PreH8 : (0 <= m)) (PreH9 : (m <= 3)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= (3 * s ))) (PreH12 : (cnt <= 3000000000)) (PreH13 : (LuxuryBlockPrefix x_pre s m cnt )),
  TT && emp 
|--
  “ (0 <= cnt) ”
  &&  “ (cnt <= 3000000000) ”
  &&  “ (LuxuryCountUpto x_pre cnt ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : (m >= 3)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (1 <= s)) (PreH5 : (s <= 1000000000)) (PreH6 : (ISqrtSpec x_pre s )) (PreH7 : (base = (s * s ))) (PreH8 : (0 <= m)) (PreH9 : (m <= 3)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= (3 * s ))) (PreH12 : (cnt <= 3000000000)) (PreH13 : (LuxuryBlockPrefix x_pre s m cnt )),
  TT && emp 
|--
  “ (LuxuryCountUpto x_pre cnt ) ”
  &&  emp
).

Definition count_upto_return_wit_1_split_goal_1 :=
forall (x_pre: Z) (cnt: Z) (m: Z) (base: Z) (s: Z) (PreH1 : (m >= 3)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (1 <= s)) (PreH5 : (s <= 1000000000)) (PreH6 : (ISqrtSpec x_pre s )) (PreH7 : (base = (s * s ))) (PreH8 : (0 <= m)) (PreH9 : (m <= 3)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= (3 * s ))) (PreH12 : (cnt <= 3000000000)) (PreH13 : (LuxuryBlockPrefix x_pre s m cnt )),
  (LuxuryCountUpto x_pre cnt )
.

Definition count_upto_return_wit_2 :=
(
forall (x_pre: Z) (PreH1 : (x_pre <= 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (0 <= 0) ”
  &&  “ (0 <= 3000000000) ”
  &&  “ (LuxuryCountUpto x_pre 0 ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre <= 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (LuxuryCountUpto x_pre 0 ) ”
  &&  emp
).

Definition count_upto_return_wit_2_split_goal_1 :=
forall (x_pre: Z) (PreH1 : (x_pre <= 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)),
  (LuxuryCountUpto x_pre 0 )
.

Definition count_upto_partial_solve_wit_1_pure :=
forall (x_pre: Z) (PreH1 : (x_pre > 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)),
  ((( &( "s" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (0 <= x_pre) ”
  &&  “ (x_pre <= 1000000000000000000) ”
.

Definition count_upto_partial_solve_wit_1_aux :=
forall (x_pre: Z) (PreH1 : (x_pre > 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (0 <= x_pre) ”
  &&  “ (x_pre <= 1000000000000000000) ”
  &&  “ (x_pre > 0) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre <= 1000000000000000000) ”
  &&  emp
.

Definition count_upto_partial_solve_wit_1 := count_upto_partial_solve_wit_1_pure -> count_upto_partial_solve_wit_1_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 3000000000)) (PreH3 : (LuxuryCountUpto (l_pre - 1 ) retval_2 )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 3000000000)) (PreH6 : (LuxuryCountUpto r_pre retval )) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 1000000000000000000)),
  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ ((retval - retval_2 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (retval - retval_2 )) ”
.

Definition solver_safety_wit_2 :=
forall (l_pre: Z) (r_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 3000000000)) (PreH3 : (LuxuryCountUpto r_pre retval )) (PreH4 : (1 <= l_pre)) (PreH5 : (l_pre <= r_pre)) (PreH6 : (r_pre <= 1000000000000000000)),
  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ ((l_pre - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (l_pre - 1 )) ”
.

Definition solver_safety_wit_3 :=
forall (l_pre: Z) (r_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 3000000000)) (PreH3 : (LuxuryCountUpto r_pre retval )) (PreH4 : (1 <= l_pre)) (PreH5 : (l_pre <= r_pre)) (PreH6 : (r_pre <= 1000000000000000000)),
  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_return_wit_1 :=
(
forall (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 3000000000)) (PreH3 : (LuxuryCountUpto (l_pre - 1 ) retval_2 )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 3000000000)) (PreH6 : (LuxuryCountUpto r_pre retval )) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (Spec l_pre r_pre (retval - retval_2 ) ) ”
  &&  emp
) \/
(
forall (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 3000000000)) (PreH3 : (LuxuryCountUpto (l_pre - 1 ) retval_2 )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 3000000000)) (PreH6 : (LuxuryCountUpto r_pre retval )) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (Spec l_pre r_pre (retval - retval_2 ) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 3000000000)) (PreH3 : (LuxuryCountUpto (l_pre - 1 ) retval_2 )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 3000000000)) (PreH6 : (LuxuryCountUpto r_pre retval )) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 1000000000000000000)),
  (Spec l_pre r_pre (retval - retval_2 ) )
.

Definition solver_partial_solve_wit_1_pure :=
forall (l_pre: Z) (r_pre: Z) (PreH1 : (1 <= l_pre)) (PreH2 : (l_pre <= r_pre)) (PreH3 : (r_pre <= 1000000000000000000)),
  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (0 <= r_pre) ”
  &&  “ (r_pre <= 1000000000000000000) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (l_pre: Z) (r_pre: Z) (PreH1 : (1 <= l_pre)) (PreH2 : (l_pre <= r_pre)) (PreH3 : (r_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (0 <= r_pre) ”
  &&  “ (r_pre <= 1000000000000000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= 1000000000000000000) ”
  &&  emp
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure :=
forall (l_pre: Z) (r_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 3000000000)) (PreH3 : (LuxuryCountUpto r_pre retval )) (PreH4 : (1 <= l_pre)) (PreH5 : (l_pre <= r_pre)) (PreH6 : (r_pre <= 1000000000000000000)),
  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (0 <= (l_pre - 1 )) ”
  &&  “ ((l_pre - 1 ) <= 1000000000000000000) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (l_pre: Z) (r_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 3000000000)) (PreH3 : (LuxuryCountUpto r_pre retval )) (PreH4 : (1 <= l_pre)) (PreH5 : (l_pre <= r_pre)) (PreH6 : (r_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (0 <= (l_pre - 1 )) ”
  &&  “ ((l_pre - 1 ) <= 1000000000000000000) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval <= 3000000000) ”
  &&  “ (LuxuryCountUpto r_pre retval ) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= 1000000000000000000) ”
  &&  emp
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_isqrt_safety_wit_1 : isqrt_safety_wit_1.
Axiom proof_of_isqrt_safety_wit_2 : isqrt_safety_wit_2.
Axiom proof_of_isqrt_safety_wit_3 : isqrt_safety_wit_3.
Axiom proof_of_isqrt_safety_wit_4 : isqrt_safety_wit_4.
Axiom proof_of_isqrt_safety_wit_5 : isqrt_safety_wit_5.
Axiom proof_of_isqrt_safety_wit_6 : isqrt_safety_wit_6.
Axiom proof_of_isqrt_safety_wit_7 : isqrt_safety_wit_7.
Axiom proof_of_isqrt_safety_wit_8 : isqrt_safety_wit_8.
Axiom proof_of_isqrt_safety_wit_9 : isqrt_safety_wit_9.
Axiom proof_of_isqrt_safety_wit_10 : isqrt_safety_wit_10.
Axiom proof_of_isqrt_safety_wit_11 : isqrt_safety_wit_11.
Axiom proof_of_isqrt_entail_wit_1 : isqrt_entail_wit_1.
Axiom proof_of_isqrt_entail_wit_2_1 : isqrt_entail_wit_2_1.
Axiom proof_of_isqrt_entail_wit_2_2 : isqrt_entail_wit_2_2.
Axiom proof_of_isqrt_return_wit_1 : isqrt_return_wit_1.
Axiom proof_of_count_upto_safety_wit_1 : count_upto_safety_wit_1.
Axiom proof_of_count_upto_safety_wit_2 : count_upto_safety_wit_2.
Axiom proof_of_count_upto_safety_wit_3 : count_upto_safety_wit_3.
Axiom proof_of_count_upto_safety_wit_4 : count_upto_safety_wit_4.
Axiom proof_of_count_upto_safety_wit_5 : count_upto_safety_wit_5.
Axiom proof_of_count_upto_safety_wit_6 : count_upto_safety_wit_6.
Axiom proof_of_count_upto_safety_wit_7 : count_upto_safety_wit_7.
Axiom proof_of_count_upto_safety_wit_8 : count_upto_safety_wit_8.
Axiom proof_of_count_upto_safety_wit_9 : count_upto_safety_wit_9.
Axiom proof_of_count_upto_safety_wit_10 : count_upto_safety_wit_10.
Axiom proof_of_count_upto_safety_wit_11 : count_upto_safety_wit_11.
Axiom proof_of_count_upto_safety_wit_12 : count_upto_safety_wit_12.
Axiom proof_of_count_upto_safety_wit_13 : count_upto_safety_wit_13.
Axiom proof_of_count_upto_safety_wit_14 : count_upto_safety_wit_14.
Axiom proof_of_count_upto_entail_wit_1 : count_upto_entail_wit_1.
Axiom proof_of_count_upto_entail_wit_2_1 : count_upto_entail_wit_2_1.
Axiom proof_of_count_upto_entail_wit_2_2 : count_upto_entail_wit_2_2.
Axiom proof_of_count_upto_return_wit_1 : count_upto_return_wit_1.
Axiom proof_of_count_upto_return_wit_2 : count_upto_return_wit_2.
Axiom proof_of_count_upto_partial_solve_wit_1_pure : count_upto_partial_solve_wit_1_pure.
Axiom proof_of_count_upto_partial_solve_wit_1 : count_upto_partial_solve_wit_1.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
