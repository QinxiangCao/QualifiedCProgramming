From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P015_2051C_preparing_for_the_exam_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (PreH1 : (Pre n_pre missing known_questions )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH7 : forall (q: Z), ((known_questions q ) -> ((1 <= q) /\ (q <= n_pre)))) (PreH8 : (m_pre = (Zlength (missing)))) (PreH9 : (KnownFlagsBridge n_pre known_questions known_flags )),
  ((( &( "only" ) )) # Int  |->_)
  **  ((( &( "unknown" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (PreH1 : (Pre n_pre missing known_questions )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH7 : forall (q: Z), ((known_questions q ) -> ((1 <= q) /\ (q <= n_pre)))) (PreH8 : (m_pre = (Zlength (missing)))) (PreH9 : (KnownFlagsBridge n_pre known_questions known_flags )),
  ((( &( "unknown" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (PreH1 : (Pre n_pre missing known_questions )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH7 : forall (q: Z), ((known_questions q ) -> ((1 <= q) /\ (q <= n_pre)))) (PreH8 : (m_pre = (Zlength (missing)))) (PreH9 : (KnownFlagsBridge n_pre known_questions known_flags )),
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "only" ) )) # Int  |-> 0)
  **  ((( &( "unknown" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : ((Znth q known_flags 0) = 0)) (PreH2 : (q <= n_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (1 <= q)) (PreH12 : (q <= (n_pre + 1 ))) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= (q - 1 ))) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ ((unknown + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (unknown + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : ((Znth q known_flags 0) = 0)) (PreH2 : (q <= n_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (1 <= q)) (PreH12 : (q <= (n_pre + 1 ))) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= (q - 1 ))) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "unknown" ) )) # Int  |-> (unknown + 1 ))
  **  ((( &( "only" ) )) # Int  |-> q)
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : ((Znth q known_flags 0) <> 0)) (PreH2 : (q <= n_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (1 <= q)) (PreH12 : (q <= (n_pre + 1 ))) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= (q - 1 ))) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : (q > n_pre)) (PreH2 : (Pre n_pre missing known_questions )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH8 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH9 : (m_pre = (Zlength (missing)))) (PreH10 : (1 <= q)) (PreH11 : (q <= (n_pre + 1 ))) (PreH12 : (0 <= unknown)) (PreH13 : (unknown <= (q - 1 ))) (PreH14 : (0 <= only)) (PreH15 : (only <= n_pre)) (PreH16 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH17 : (KnownFlagsBridge n_pre known_questions known_flags )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : ((Znth i missing 0) = only)) (PreH2 : (unknown = 1)) (PreH3 : (unknown <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (Pre n_pre missing known_questions )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH11 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH12 : (m_pre = (Zlength (missing)))) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (0 <= unknown)) (PreH16 : (unknown <= n_pre)) (PreH17 : (0 <= only)) (PreH18 : (only <= n_pre)) (PreH19 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH20 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH21 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full res_pre (i + 1 ) (app (result_bytes) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (IntArray.full a_pre m_pre missing )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown = 0)) (PreH2 : (i < m_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= n_pre)) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH18 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH19 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full res_pre (i + 1 ) (app (result_bytes) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown <> 1)) (PreH2 : (unknown <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (Pre n_pre missing known_questions )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH10 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH11 : (m_pre = (Zlength (missing)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= unknown)) (PreH15 : (unknown <= n_pre)) (PreH16 : (0 <= only)) (PreH17 : (only <= n_pre)) (PreH18 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH19 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH20 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full res_pre (i + 1 ) (app (result_bytes) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : ((Znth i missing 0) <> only)) (PreH2 : (unknown = 1)) (PreH3 : (unknown <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (Pre n_pre missing known_questions )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH11 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH12 : (m_pre = (Zlength (missing)))) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (0 <= unknown)) (PreH16 : (unknown <= n_pre)) (PreH17 : (0 <= only)) (PreH18 : (only <= n_pre)) (PreH19 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH20 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH21 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full res_pre (i + 1 ) (app (result_bytes) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (IntArray.full a_pre m_pre missing )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_12 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (Pre n_pre missing known_questions )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH8 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH9 : (m_pre = (Zlength (missing)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= unknown)) (PreH13 : (unknown <= n_pre)) (PreH14 : (0 <= only)) (PreH15 : (only <= n_pre)) (PreH16 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH17 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown <> 0)) (PreH2 : (i < m_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= n_pre)) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH18 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH19 : (KnownFlagsBridge n_pre known_questions known_flags )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : ((Znth i missing 0) = only)) (PreH2 : (unknown = 1)) (PreH3 : (unknown <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (Pre n_pre missing known_questions )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH11 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH12 : (m_pre = (Zlength (missing)))) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (0 <= unknown)) (PreH16 : (unknown <= n_pre)) (PreH17 : (0 <= only)) (PreH18 : (only <= n_pre)) (PreH19 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH20 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH21 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (IntArray.full a_pre m_pre missing )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (49 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_15 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown = 0)) (PreH2 : (i < m_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= n_pre)) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH18 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH19 : (KnownFlagsBridge n_pre known_questions known_flags )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (49 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_16 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown <> 1)) (PreH2 : (unknown <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (Pre n_pre missing known_questions )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH10 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH11 : (m_pre = (Zlength (missing)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= unknown)) (PreH15 : (unknown <= n_pre)) (PreH16 : (0 <= only)) (PreH17 : (only <= n_pre)) (PreH18 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH19 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH20 : (KnownFlagsBridge n_pre known_questions known_flags )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (48 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 48) ”
.

Definition solver_safety_wit_17 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : ((Znth i missing 0) <> only)) (PreH2 : (unknown = 1)) (PreH3 : (unknown <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (Pre n_pre missing known_questions )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH11 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH12 : (m_pre = (Zlength (missing)))) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (0 <= unknown)) (PreH16 : (unknown <= n_pre)) (PreH17 : (0 <= only)) (PreH18 : (only <= n_pre)) (PreH19 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH20 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH21 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (IntArray.full a_pre m_pre missing )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (48 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 48) ”
.

Definition solver_safety_wit_18 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (Pre n_pre missing known_questions )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH8 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH9 : (m_pre = (Zlength (missing)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= unknown)) (PreH13 : (unknown <= n_pre)) (PreH14 : (0 <= only)) (PreH15 : (only <= n_pre)) (PreH16 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH17 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "known" ) )) # Ptr  |-> known_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res_pre)
  **  ((( &( "unknown" ) )) # Int  |-> unknown)
  **  ((( &( "only" ) )) # Int  |-> only)
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_entail_wit_1 :=
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (PreH1 : (Pre n_pre missing known_questions )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 missing 0)) /\ ((Znth i_2 missing 0) <= n_pre)))) (PreH7 : forall (q: Z), ((known_questions q ) -> ((1 <= q) /\ (q <= n_pre)))) (PreH8 : (m_pre = (Zlength (missing)))) (PreH9 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (1 - 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions 1 0 0 ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
) \/
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (Pre n_pre missing known_questions )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 missing 0)) /\ ((Znth i_2 missing 0) <= n_pre)))) (PreH7 : forall (q: Z), ((known_questions q ) -> ((1 <= q) /\ (q <= n_pre)))) (PreH8 : (m_pre = (Zlength (missing)))) (PreH9 : (KnownFlagsBridge n_pre known_questions known_flags )),
  TT && emp 
|--
  “ (UnknownPrefixSummary n_pre known_questions 1 0 0 ) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (Pre n_pre missing known_questions )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 missing 0)) /\ ((Znth i_2 missing 0) <= n_pre)))) (PreH7 : forall (q: Z), ((known_questions q ) -> ((1 <= q) /\ (q <= n_pre)))) (PreH8 : (m_pre = (Zlength (missing)))) (PreH9 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (UnknownPrefixSummary n_pre known_questions 1 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (Pre n_pre missing known_questions )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 missing 0)) /\ ((Znth i_2 missing 0) <= n_pre)))) (PreH7 : forall (q: Z), ((known_questions q ) -> ((1 <= q) /\ (q <= n_pre)))) (PreH8 : (m_pre = (Zlength (missing)))) (PreH9 : (KnownFlagsBridge n_pre known_questions known_flags )),
  forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (Pre n_pre missing known_questions )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 missing 0)) /\ ((Znth i_2 missing 0) <= n_pre)))) (PreH7 : forall (q: Z), ((known_questions q ) -> ((1 <= q) /\ (q <= n_pre)))) (PreH8 : (m_pre = (Zlength (missing)))) (PreH9 : (KnownFlagsBridge n_pre known_questions known_flags )),
  forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))
.

Definition solver_entail_wit_2_1 :=
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : ((Znth q known_flags 0) = 0)) (PreH2 : (q <= n_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (1 <= q)) (PreH12 : (q <= (n_pre + 1 ))) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= (q - 1 ))) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (1 <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= (n_pre + 1 )) ”
  &&  “ (0 <= (unknown + 1 )) ”
  &&  “ ((unknown + 1 ) <= ((q + 1 ) - 1 )) ”
  &&  “ (0 <= q) ”
  &&  “ (q <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (q + 1 ) (unknown + 1 ) q ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
) \/
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : ((Znth q known_flags 0) = 0)) (PreH2 : (q <= n_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (1 <= q)) (PreH12 : (q <= (n_pre + 1 ))) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= (q - 1 ))) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  TT && emp 
|--
  “ (UnknownPrefixSummary n_pre known_questions (q + 1 ) (unknown + 1 ) q ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : ((Znth q known_flags 0) = 0)) (PreH2 : (q <= n_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (1 <= q)) (PreH12 : (q <= (n_pre + 1 ))) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= (q - 1 ))) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (UnknownPrefixSummary n_pre known_questions (q + 1 ) (unknown + 1 ) q )
.

Definition solver_entail_wit_2_2 :=
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : ((Znth q known_flags 0) <> 0)) (PreH2 : (q <= n_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (1 <= q)) (PreH12 : (q <= (n_pre + 1 ))) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= (q - 1 ))) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (1 <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= (n_pre + 1 )) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= ((q + 1 ) - 1 )) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (q + 1 ) unknown only ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
) \/
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : ((Znth q known_flags 0) <> 0)) (PreH2 : (q <= n_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (1 <= q)) (PreH12 : (q <= (n_pre + 1 ))) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= (q - 1 ))) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  TT && emp 
|--
  “ (UnknownPrefixSummary n_pre known_questions (q + 1 ) unknown only ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : ((Znth q known_flags 0) <> 0)) (PreH2 : (q <= n_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (1 <= q)) (PreH12 : (q <= (n_pre + 1 ))) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= (q - 1 ))) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (UnknownPrefixSummary n_pre known_questions (q + 1 ) unknown only )
.

Definition solver_entail_wit_3 :=
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : (q > n_pre)) (PreH2 : (Pre n_pre missing known_questions )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH8 : forall (x_2: Z), ((known_questions x_2 ) -> ((1 <= x_2) /\ (x_2 <= n_pre)))) (PreH9 : (m_pre = (Zlength (missing)))) (PreH10 : (1 <= q)) (PreH11 : (q <= (n_pre + 1 ))) (PreH12 : (0 <= unknown)) (PreH13 : (unknown <= (q - 1 ))) (PreH14 : (0 <= only)) (PreH15 : (only <= n_pre)) (PreH16 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH17 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  EX (out: (@list Z)) (result_bytes: (@list Z)),
  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions 0 out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre 0 result_bytes )
  **  (CharArray.undef_seg res_pre 0 (m_pre + 1 ) )
) \/
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : (q > n_pre)) (PreH2 : (Pre n_pre missing known_questions )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH8 : forall (x_2: Z), ((known_questions x_2 ) -> ((1 <= x_2) /\ (x_2 <= n_pre)))) (PreH9 : (m_pre = (Zlength (missing)))) (PreH10 : (1 <= q)) (PreH11 : (q <= (n_pre + 1 ))) (PreH12 : (0 <= unknown)) (PreH13 : (unknown <= (q - 1 ))) (PreH14 : (0 <= only)) (PreH15 : (only <= n_pre)) (PreH16 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH17 : (KnownFlagsBridge n_pre known_questions known_flags )),
  TT && emp 
|--
  EX (out: (@list Z)),
  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (missing))) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions 0 out (@nil Z) ) ”
  &&  emp
).

Definition solver_entail_wit_4_1 :=
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out_2: (@list Z)) (result_bytes_2: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : ((Znth i missing 0) = only)) (PreH2 : (unknown = 1)) (PreH3 : (unknown <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (Pre n_pre missing known_questions )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH11 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH12 : (m_pre = (Zlength (missing)))) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (0 <= unknown)) (PreH16 : (unknown <= n_pre)) (PreH17 : (0 <= only)) (PreH18 : (only <= n_pre)) (PreH19 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH20 : (ResultPrefix n_pre missing known_questions i out_2 result_bytes_2 )) (PreH21 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full res_pre (i + 1 ) (app (result_bytes_2) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
|--
  EX (out: (@list Z)) (result_bytes: (@list Z)),
  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions (i + 1 ) out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre (i + 1 ) result_bytes )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
) \/
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (out_2: (@list Z)) (result_bytes_2: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : ((Znth i missing 0) = only)) (PreH2 : (unknown = 1)) (PreH3 : (unknown <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (Pre n_pre missing known_questions )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH11 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH12 : (m_pre = (Zlength (missing)))) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (0 <= unknown)) (PreH16 : (unknown <= n_pre)) (PreH17 : (0 <= only)) (PreH18 : (only <= n_pre)) (PreH19 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH20 : (ResultPrefix n_pre missing known_questions i out_2 result_bytes_2 )) (PreH21 : (KnownFlagsBridge n_pre known_questions known_flags )),
  TT && emp 
|--
  EX (out: (@list Z)),
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (missing))) ”
  &&  “ (ResultPrefix n_pre missing known_questions (i + 1 ) out (app (result_bytes_2) ((cons (49) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_4_2 :=
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out_2: (@list Z)) (result_bytes_2: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown = 0)) (PreH2 : (i < m_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= n_pre)) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH18 : (ResultPrefix n_pre missing known_questions i out_2 result_bytes_2 )) (PreH19 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full res_pre (i + 1 ) (app (result_bytes_2) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
|--
  EX (out: (@list Z)) (result_bytes: (@list Z)),
  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions (i + 1 ) out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre (i + 1 ) result_bytes )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
) \/
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (out_2: (@list Z)) (result_bytes_2: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown = 0)) (PreH2 : (i < m_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= n_pre)) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH18 : (ResultPrefix n_pre missing known_questions i out_2 result_bytes_2 )) (PreH19 : (KnownFlagsBridge n_pre known_questions known_flags )),
  TT && emp 
|--
  EX (out: (@list Z)),
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (missing))) ”
  &&  “ (ResultPrefix n_pre missing known_questions (i + 1 ) out (app (result_bytes_2) ((cons (49) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_4_3 :=
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out_2: (@list Z)) (result_bytes_2: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown <> 1)) (PreH2 : (unknown <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (Pre n_pre missing known_questions )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH10 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH11 : (m_pre = (Zlength (missing)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= unknown)) (PreH15 : (unknown <= n_pre)) (PreH16 : (0 <= only)) (PreH17 : (only <= n_pre)) (PreH18 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH19 : (ResultPrefix n_pre missing known_questions i out_2 result_bytes_2 )) (PreH20 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full res_pre (i + 1 ) (app (result_bytes_2) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
|--
  EX (out: (@list Z)) (result_bytes: (@list Z)),
  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions (i + 1 ) out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre (i + 1 ) result_bytes )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
) \/
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (out_2: (@list Z)) (result_bytes_2: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown <> 1)) (PreH2 : (unknown <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (Pre n_pre missing known_questions )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH10 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH11 : (m_pre = (Zlength (missing)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= unknown)) (PreH15 : (unknown <= n_pre)) (PreH16 : (0 <= only)) (PreH17 : (only <= n_pre)) (PreH18 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH19 : (ResultPrefix n_pre missing known_questions i out_2 result_bytes_2 )) (PreH20 : (KnownFlagsBridge n_pre known_questions known_flags )),
  TT && emp 
|--
  EX (out: (@list Z)),
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (missing))) ”
  &&  “ (ResultPrefix n_pre missing known_questions (i + 1 ) out (app (result_bytes_2) ((cons (48) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_4_4 :=
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out_2: (@list Z)) (result_bytes_2: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : ((Znth i missing 0) <> only)) (PreH2 : (unknown = 1)) (PreH3 : (unknown <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (Pre n_pre missing known_questions )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH11 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH12 : (m_pre = (Zlength (missing)))) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (0 <= unknown)) (PreH16 : (unknown <= n_pre)) (PreH17 : (0 <= only)) (PreH18 : (only <= n_pre)) (PreH19 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH20 : (ResultPrefix n_pre missing known_questions i out_2 result_bytes_2 )) (PreH21 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full res_pre (i + 1 ) (app (result_bytes_2) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
|--
  EX (out: (@list Z)) (result_bytes: (@list Z)),
  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions (i + 1 ) out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre (i + 1 ) result_bytes )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
) \/
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (out_2: (@list Z)) (result_bytes_2: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : ((Znth i missing 0) <> only)) (PreH2 : (unknown = 1)) (PreH3 : (unknown <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (Pre n_pre missing known_questions )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH11 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH12 : (m_pre = (Zlength (missing)))) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (0 <= unknown)) (PreH16 : (unknown <= n_pre)) (PreH17 : (0 <= only)) (PreH18 : (only <= n_pre)) (PreH19 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH20 : (ResultPrefix n_pre missing known_questions i out_2 result_bytes_2 )) (PreH21 : (KnownFlagsBridge n_pre known_questions known_flags )),
  TT && emp 
|--
  EX (out: (@list Z)),
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (missing))) ”
  &&  “ (ResultPrefix n_pre missing known_questions (i + 1 ) out (app (result_bytes_2) ((cons (48) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_return_wit_1 :=
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out_2: (@list Z)) (result_bytes_2: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (Pre n_pre missing known_questions )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH8 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH9 : (m_pre = (Zlength (missing)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= unknown)) (PreH13 : (unknown <= n_pre)) (PreH14 : (0 <= only)) (PreH15 : (only <= n_pre)) (PreH16 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH17 : (ResultPrefix n_pre missing known_questions i out_2 result_bytes_2 )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full res_pre (i + 1 ) (app (result_bytes_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
|--
  EX (result_bytes: (@list Z)) (out: (@list Z)),
  “ (Spec n_pre missing known_questions out ) ”
  &&  “ (ResultStringBridge out result_bytes ) ”
  &&  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre (m_pre + 1 ) result_bytes )
) \/
(
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (m_pre: Z) (res_pre: Z) (out_2: (@list Z)) (result_bytes_2: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (Pre n_pre missing known_questions )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH8 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH9 : (m_pre = (Zlength (missing)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= unknown)) (PreH13 : (unknown <= n_pre)) (PreH14 : (0 <= only)) (PreH15 : (only <= n_pre)) (PreH16 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH17 : (ResultPrefix n_pre missing known_questions i out_2 result_bytes_2 )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full res_pre (i + 1 ) (app (result_bytes_2) ((cons (0) ((@nil Z))))) )
|--
  EX (result_bytes: (@list Z)) (out: (@list Z)),
  “ (Spec n_pre missing known_questions out ) ”
  &&  “ (ResultStringBridge out result_bytes ) ”
  &&  (CharArray.full res_pre (m_pre + 1 ) result_bytes )
).

Definition solver_partial_solve_wit_1 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (only: Z) (unknown: Z) (q: Z) (PreH1 : (q <= n_pre)) (PreH2 : (Pre n_pre missing known_questions )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre)))) (PreH8 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH9 : (m_pre = (Zlength (missing)))) (PreH10 : (1 <= q)) (PreH11 : (q <= (n_pre + 1 ))) (PreH12 : (0 <= unknown)) (PreH13 : (unknown <= (q - 1 ))) (PreH14 : (0 <= only)) (PreH15 : (only <= n_pre)) (PreH16 : (UnknownPrefixSummary n_pre known_questions q unknown only )) (PreH17 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
|--
  “ (q <= n_pre) ”
  &&  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((1 <= (Znth i missing 0)) /\ ((Znth i missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (1 <= q) ”
  &&  “ (q <= (n_pre + 1 )) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= (q - 1 )) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions q unknown only ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (((known_pre + (q * sizeof(CHAR)))) # Char  |-> (Znth q known_flags 0))
  **  (CharArray.missing_i known_pre q 0 (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.undef_full res_pre (m_pre + 1 ) )
.

Definition solver_partial_solve_wit_2 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown = 1)) (PreH2 : (unknown <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (Pre n_pre missing known_questions )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH10 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH11 : (m_pre = (Zlength (missing)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= unknown)) (PreH15 : (unknown <= n_pre)) (PreH16 : (0 <= only)) (PreH17 : (only <= n_pre)) (PreH18 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH19 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH20 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (unknown = 1) ”
  &&  “ (unknown <> 0) ”
  &&  “ (i < m_pre) ”
  &&  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions i out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i missing 0))
  **  (IntArray.missing_i a_pre i 0 m_pre missing )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
.

Definition solver_partial_solve_wit_3 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : ((Znth i missing 0) = only)) (PreH2 : (unknown = 1)) (PreH3 : (unknown <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (Pre n_pre missing known_questions )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH11 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH12 : (m_pre = (Zlength (missing)))) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (0 <= unknown)) (PreH16 : (unknown <= n_pre)) (PreH17 : (0 <= only)) (PreH18 : (only <= n_pre)) (PreH19 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH20 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH21 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ ((Znth i missing 0) = only) ”
  &&  “ (unknown = 1) ”
  &&  “ (unknown <> 0) ”
  &&  “ (i < m_pre) ”
  &&  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions i out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (((res_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (CharArray.full res_pre i result_bytes )
.

Definition solver_partial_solve_wit_4 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown = 0)) (PreH2 : (i < m_pre)) (PreH3 : (Pre n_pre missing known_questions )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH9 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH10 : (m_pre = (Zlength (missing)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= unknown)) (PreH14 : (unknown <= n_pre)) (PreH15 : (0 <= only)) (PreH16 : (only <= n_pre)) (PreH17 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH18 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH19 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (unknown = 0) ”
  &&  “ (i < m_pre) ”
  &&  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions i out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (((res_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
.

Definition solver_partial_solve_wit_5 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (unknown <> 1)) (PreH2 : (unknown <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (Pre n_pre missing known_questions )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH10 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH11 : (m_pre = (Zlength (missing)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= unknown)) (PreH15 : (unknown <= n_pre)) (PreH16 : (0 <= only)) (PreH17 : (only <= n_pre)) (PreH18 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH19 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH20 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (unknown <> 1) ”
  &&  “ (unknown <> 0) ”
  &&  “ (i < m_pre) ”
  &&  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions i out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (((res_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
.

Definition solver_partial_solve_wit_6 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : ((Znth i missing 0) <> only)) (PreH2 : (unknown = 1)) (PreH3 : (unknown <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (Pre n_pre missing known_questions )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH11 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH12 : (m_pre = (Zlength (missing)))) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (0 <= unknown)) (PreH16 : (unknown <= n_pre)) (PreH17 : (0 <= only)) (PreH18 : (only <= n_pre)) (PreH19 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH20 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH21 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ ((Znth i missing 0) <> only) ”
  &&  “ (unknown = 1) ”
  &&  “ (unknown <> 0) ”
  &&  “ (i < m_pre) ”
  &&  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions i out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (((res_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg res_pre (i + 1 ) (m_pre + 1 ) )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (CharArray.full res_pre i result_bytes )
.

Definition solver_partial_solve_wit_7 :=
forall (known_flags: (@list Z)) (known_questions: (Z -> Prop)) (missing: (@list Z)) (n_pre: Z) (known_pre: Z) (a_pre: Z) (m_pre: Z) (res_pre: Z) (out: (@list Z)) (result_bytes: (@list Z)) (only: Z) (unknown: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (Pre n_pre missing known_questions )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre)))) (PreH8 : forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre)))) (PreH9 : (m_pre = (Zlength (missing)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= unknown)) (PreH13 : (unknown <= n_pre)) (PreH14 : (0 <= only)) (PreH15 : (only <= n_pre)) (PreH16 : (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only )) (PreH17 : (ResultPrefix n_pre missing known_questions i out result_bytes )) (PreH18 : (KnownFlagsBridge n_pre known_questions known_flags )),
  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
  **  (CharArray.undef_seg res_pre i (m_pre + 1 ) )
|--
  “ (i >= m_pre) ”
  &&  “ (Pre n_pre missing known_questions ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < m_pre)) -> ((1 <= (Znth j missing 0)) /\ ((Znth j missing 0) <= n_pre))) ”
  &&  “ forall (x: Z), ((known_questions x ) -> ((1 <= x) /\ (x <= n_pre))) ”
  &&  “ (m_pre = (Zlength (missing))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= unknown) ”
  &&  “ (unknown <= n_pre) ”
  &&  “ (0 <= only) ”
  &&  “ (only <= n_pre) ”
  &&  “ (UnknownPrefixSummary n_pre known_questions (n_pre + 1 ) unknown only ) ”
  &&  “ (ResultPrefix n_pre missing known_questions i out result_bytes ) ”
  &&  “ (KnownFlagsBridge n_pre known_questions known_flags ) ”
  &&  (((res_pre + (m_pre * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i res_pre m_pre i (m_pre + 1 ) )
  **  (CharArray.full known_pre (n_pre + 1 ) known_flags )
  **  (IntArray.full a_pre m_pre missing )
  **  (CharArray.full res_pre i result_bytes )
.

Module Type VC_Correct.


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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
