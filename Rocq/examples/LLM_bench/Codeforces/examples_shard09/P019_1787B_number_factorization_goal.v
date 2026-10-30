From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P019_1787B_number_factorization_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)),
  ((( &( "m" ) )) # Int  |->_)
  **  (Int64Array.undef_full ( &( "ex" ) ) 40 )
  **  (Int64Array.undef_full ( &( "pr" ) ) 40 )
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)),
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  (Int64Array.undef_full ( &( "ex" ) ) 40 )
  **  (Int64Array.undef_full ( &( "pr" ) ) 40 )
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_3 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= n)) (PreH4 : (n <= n_pre)) (PreH5 : (2 <= d)) (PreH6 : (d <= n_pre)) (PreH7 : ((d * d ) <= 1000000000000000000)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps)) = m)) (PreH11 : ((Zlength (es)) = m)) (PreH12 : (FactorScan n_pre n d ps es )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((d * d ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (d * d )) ”
.

Definition solver_safety_wit_4 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((d * d ) <= n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : ((d * d ) <= 1000000000000000000)) (PreH9 : (0 <= m)) (PreH10 : (m <= 29)) (PreH11 : ((Zlength (ps)) = m)) (PreH12 : ((Zlength (es)) = m)) (PreH13 : (FactorScan n_pre n d ps es )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((n <> (INT64_MIN)) \/ (d <> (-1))) ”
  &&  “ (d <> 0) ”
.

Definition solver_safety_wit_5 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((d * d ) <= n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : ((d * d ) <= 1000000000000000000)) (PreH9 : (0 <= m)) (PreH10 : (m <= 29)) (PreH11 : ((Zlength (ps)) = m)) (PreH12 : ((Zlength (es)) = m)) (PreH13 : (FactorScan n_pre n d ps es )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : ((d * d ) <= n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps)) = m)) (PreH13 : ((Zlength (es)) = m)) (PreH14 : (FactorScan n_pre n d ps es )),
  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= n)) (PreH4 : (n <= n_pre)) (PreH5 : (2 <= d)) (PreH6 : (d <= n_pre)) (PreH7 : (0 <= m)) (PreH8 : (m <= 29)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (ExtractionScale n d e )) (PreH12 : (FactorExtract n_pre n d ps es e )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ ((n <> (INT64_MIN)) \/ (d <> (-1))) ”
  &&  “ (d <> 0) ”
.

Definition solver_safety_wit_8 :=
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= n)) (PreH4 : (n <= n_pre)) (PreH5 : (2 <= d)) (PreH6 : (d <= n_pre)) (PreH7 : (0 <= m)) (PreH8 : (m <= 29)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (ExtractionScale n d e )) (PreH12 : (FactorExtract n_pre n d ps es e )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps)) = m)) (PreH11 : ((Zlength (es)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps es e )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ ((n <> (INT64_MIN)) \/ (d <> (-1))) ”
  &&  “ (d <> 0) ”
.

Definition solver_safety_wit_10 :=
(
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps)) = m)) (PreH11 : ((Zlength (es)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps es e )),
  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int64  |-> (n ÷ d ))
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ (((Znth (m - 0 ) (app (es) ((cons (e) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (m - 0 ) (app (es) ((cons (e) ((@nil Z))))) 0) + 1 )) ”
) \/
(
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps)) = m)) (PreH11 : ((Zlength (es)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps es e )),
  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int64  |-> (n ÷ d ))
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ (((Znth (m - 0 ) (app (es) ((cons (e) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (m - 0 ) (app (es) ((cons (e) ((@nil Z))))) 0) + 1 )) ”
).

Definition solver_safety_wit_10_split_goal_1 :=
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps)) = m)) (PreH11 : ((Zlength (es)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps es e )),
  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int64  |-> (n ÷ d ))
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ (((Znth (m - 0 ) (app (es) ((cons (e) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_10_split_goal_2 :=
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps)) = m)) (PreH11 : ((Zlength (es)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps es e )),
  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int64  |-> (n ÷ d ))
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ ((INT64_MIN) <= ((Znth (m - 0 ) (app (es) ((cons (e) ((@nil Z))))) 0) + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps)) = m)) (PreH11 : ((Zlength (es)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps es e )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ ((m + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (m + 1 )) ”
.

Definition solver_safety_wit_12 :=
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps)) = m)) (PreH11 : ((Zlength (es)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps es e )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ ((d + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps)) = m)) (PreH13 : ((Zlength (es)) = m)) (PreH14 : (FactorScan n_pre n d ps es )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((d + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((d * d ) > n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : ((d * d ) <= 1000000000000000000)) (PreH9 : (0 <= m)) (PreH10 : (m <= 29)) (PreH11 : ((Zlength (ps)) = m)) (PreH12 : ((Zlength (es)) = m)) (PreH13 : (FactorScan n_pre n d ps es )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n > 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps)) = m)) (PreH13 : ((Zlength (es)) = m)) (PreH14 : (FactorScan n_pre n d ps es )),
  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (n) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n > 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps)) = m)) (PreH13 : ((Zlength (es)) = m)) (PreH14 : (FactorScan n_pre n d ps es )),
  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (1) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (n) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
|--
  “ ((m + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (m + 1 )) ”
.

Definition solver_safety_wit_17 :=
forall (n_pre: Z) (ps: (@list Z)) (es: (@list Z)) (n: Z) (m: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= n)) (PreH4 : (n <= n_pre)) (PreH5 : (1 <= m)) (PreH6 : (m <= 30)) (PreH7 : ((Zlength (ps)) = m)) (PreH8 : ((Zlength (es)) = m)) (PreH9 : (PrimeFactorization n_pre ps es )),
  ((( &( "maxe" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 :=
forall (n_pre: Z) (ps: (@list Z)) (es: (@list Z)) (n: Z) (m: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= n)) (PreH4 : (n <= n_pre)) (PreH5 : (1 <= m)) (PreH6 : (m <= 30)) (PreH7 : ((Zlength (ps)) = m)) (PreH8 : ((Zlength (es)) = m)) (PreH9 : (PrimeFactorization n_pre ps es )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "maxe" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es i maxe )) (PreH13 : (PrimeFactorization n_pre ps es )),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_20 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es 0) > maxe)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (0 <= i)) (PreH12 : (i <= m)) (PreH13 : (PrefixMaximum es i maxe )) (PreH14 : (PrimeFactorization n_pre ps es )),
  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "maxe" ) )) # Int64  |-> (Znth (i - 0 ) es 0))
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_21 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es 0) <= maxe)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (0 <= i)) (PreH12 : (i <= m)) (PreH13 : (PrefixMaximum es i maxe )) (PreH14 : (PrimeFactorization n_pre ps es )),
  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_22 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es i maxe )) (PreH13 : (PrimeFactorization n_pre ps es )),
  ((( &( "k" ) )) # Int64  |->_)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_23 :=
forall (n_pre: Z) (total: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (k <= maxe)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= (maxe + 1 ))) (PreH14 : (MaximumExponent es maxe )) (PreH15 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH16 : (LayerSumPrefix n_pre ps es maxe k total )),
  ((( &( "prod" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24 :=
forall (n_pre: Z) (total: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (k <= maxe)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= (maxe + 1 ))) (PreH14 : (MaximumExponent es maxe )) (PreH15 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH16 : (LayerSumPrefix n_pre ps es maxe k total )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "prod" ) )) # Int64  |-> 1)
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_25 :=
(
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es 0) >= k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH19 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps es k i prod )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prod" ) )) # Int64  |-> prod)
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((prod * (Znth (i - 0 ) ps 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (prod * (Znth (i - 0 ) ps 0) )) ”
) \/
(
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es 0) >= k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH19 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps es k i prod )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prod" ) )) # Int64  |-> prod)
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((prod * (Znth (i - 0 ) ps 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (prod * (Znth (i - 0 ) ps 0) )) ”
).

Definition solver_safety_wit_25_split_goal_1 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es 0) >= k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH19 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps es k i prod )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prod" ) )) # Int64  |-> prod)
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((prod * (Znth (i - 0 ) ps 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_25_split_goal_2 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es 0) >= k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH19 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps es k i prod )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prod" ) )) # Int64  |-> prod)
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((INT64_MIN) <= (prod * (Znth (i - 0 ) ps 0) )) ”
.

Definition solver_safety_wit_26 :=
(
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= maxe)) (PreH14 : (0 <= i)) (PreH15 : (i <= m)) (PreH16 : (MaximumExponent es maxe )) (PreH17 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH18 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH19 : (LayerProductPrefix n_pre ps es k i prod )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prod" ) )) # Int64  |-> prod)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((total + prod ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + prod )) ”
) \/
(
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= maxe)) (PreH14 : (0 <= i)) (PreH15 : (i <= m)) (PreH16 : (MaximumExponent es maxe )) (PreH17 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH18 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH19 : (LayerProductPrefix n_pre ps es k i prod )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prod" ) )) # Int64  |-> prod)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((total + prod ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + prod )) ”
).

Definition solver_safety_wit_26_split_goal_1 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= maxe)) (PreH14 : (0 <= i)) (PreH15 : (i <= m)) (PreH16 : (MaximumExponent es maxe )) (PreH17 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH18 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH19 : (LayerProductPrefix n_pre ps es k i prod )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prod" ) )) # Int64  |-> prod)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((total + prod ) <= INT64_MAX) ”
.

Definition solver_safety_wit_26_split_goal_2 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= maxe)) (PreH14 : (0 <= i)) (PreH15 : (i <= m)) (PreH16 : (MaximumExponent es maxe )) (PreH17 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH18 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH19 : (LayerProductPrefix n_pre ps es k i prod )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prod" ) )) # Int64  |-> prod)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((INT64_MIN) <= (total + prod )) ”
.

Definition solver_safety_wit_27 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es 0) >= k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH19 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps es k i prod )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prod" ) )) # Int64  |-> (prod * (Znth (i - 0 ) ps 0) ))
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_28 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es 0) < k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH19 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps es k i prod )),
  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prod" ) )) # Int64  |-> prod)
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_29 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= maxe)) (PreH14 : (0 <= i)) (PreH15 : (i <= m)) (PreH16 : (MaximumExponent es maxe )) (PreH17 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH18 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH19 : (LayerProductPrefix n_pre ps es k i prod )),
  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "maxe" ) )) # Int64  |-> maxe)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  ((( &( "total" ) )) # Int64  |-> (total + prod ))
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((k + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (k + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)),
  (Int64Array.undef_full ( &( "ex" ) ) 40 )
  **  (Int64Array.undef_full ( &( "pr" ) ) 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= n_pre) ”
  &&  “ ((2 * 2 ) <= 1000000000000000000) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 29) ”
  &&  “ ((Zlength (ps)) = 0) ”
  &&  “ ((Zlength (es)) = 0) ”
  &&  “ (FactorScan n_pre n_pre 2 ps es ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 0 ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) 0 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 0 es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) 0 40 )
) \/
(
forall (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)),
  TT && emp 
|--
  “ (FactorScan n_pre n_pre 2 (@nil Z) (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)),
  (FactorScan n_pre n_pre 2 (@nil Z) (@nil Z) )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)),
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)),
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_2 :=
(
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : ((d * d ) <= n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es_2) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps_2) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
|--
  EX (e: Z) (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= n_pre) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= 29) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (ExtractionScale n d e ) ”
  &&  “ (FactorExtract n_pre n d ps es e ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
) \/
(
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : ((d * d ) <= n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  TT && emp 
|--
  EX (e: Z) (es: (@list Z)) (ps: (@list Z)),
  “ ((app (ps_2) ((cons (d) ((@nil Z))))) = (app (ps) ((cons (d) ((@nil Z)))))) ”
  &&  “ ((app (es_2) ((cons (0) ((@nil Z))))) = (app (es) ((cons (e) ((@nil Z)))))) ”
  &&  “ ((Zlength (ps)) = (Zlength (ps_2))) ”
  &&  “ ((Zlength (es)) = (Zlength (ps_2))) ”
  &&  “ (ExtractionScale n d e ) ”
  &&  “ (FactorExtract n_pre n d ps es e ) ”
  &&  emp
).

Definition solver_entail_wit_3 :=
(
forall (n_pre: Z) (e_2: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps_2)) = m)) (PreH11 : ((Zlength (es_2)) = m)) (PreH12 : (ExtractionScale n d e_2 )) (PreH13 : (FactorExtract n_pre n d ps_2 es_2 e_2 )),
  (Int64Array.full ( &( "ex" ) ) (m + 1 ) (replace_Znth (m) (((Znth (m - 0 ) (app (es_2) ((cons (e_2) ((@nil Z))))) 0) + 1 )) ((app (es_2) ((cons (e_2) ((@nil Z))))))) )
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps_2) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  EX (e: Z) (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= (n ÷ d )) ”
  &&  “ ((n ÷ d ) <= n_pre) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= n_pre) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= 29) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (ExtractionScale (n ÷ d ) d e ) ”
  &&  “ (FactorExtract n_pre (n ÷ d ) d ps es e ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
) \/
(
forall (n_pre: Z) (e_2: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps_2)) = m)) (PreH11 : ((Zlength (es_2)) = m)) (PreH12 : (ExtractionScale n d e_2 )) (PreH13 : (FactorExtract n_pre n d ps_2 es_2 e_2 )),
  (Int64Array.full ( &( "ex" ) ) (m + 1 ) (replace_Znth (m) (((Znth (m - 0 ) (app (es_2) ((cons (e_2) ((@nil Z))))) 0) + 1 )) ((app (es_2) ((cons (e_2) ((@nil Z))))))) )
|--
  EX (e: Z) (es: (@list Z)) (ps: (@list Z)),
  “ ((app (ps_2) ((cons (d) ((@nil Z))))) = (app (ps) ((cons (d) ((@nil Z)))))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= (n ÷ d )) ”
  &&  “ ((n ÷ d ) <= n_pre) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= n_pre) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= 29) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (ExtractionScale (n ÷ d ) d e ) ”
  &&  “ (FactorExtract n_pre (n ÷ d ) d ps es e ) ”
  &&  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
).

Definition solver_entail_wit_4_1 :=
(
forall (n_pre: Z) (e: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps_2)) = m)) (PreH11 : ((Zlength (es_2)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps_2 es_2 e )),
  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps_2) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es_2) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (2 <= (d + 1 )) ”
  &&  “ ((d + 1 ) <= n_pre) ”
  &&  “ (((d + 1 ) * (d + 1 ) ) <= 1000000000000000000) ”
  &&  “ (0 <= (m + 1 )) ”
  &&  “ ((m + 1 ) <= 29) ”
  &&  “ ((Zlength (ps)) = (m + 1 )) ”
  &&  “ ((Zlength (es)) = (m + 1 )) ”
  &&  “ (FactorScan n_pre n (d + 1 ) ps es ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
) \/
(
forall (n_pre: Z) (e: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps_2)) = m)) (PreH11 : ((Zlength (es_2)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps_2 es_2 e )),
  TT && emp 
|--
  “ (FactorScan n_pre n (d + 1 ) (app (ps_2) ((cons (d) ((@nil Z))))) (app (es_2) ((cons (e) ((@nil Z))))) ) ”
  &&  “ ((Zlength ((app (es_2) ((cons (e) ((@nil Z))))))) = (m + 1 )) ”
  &&  “ ((Zlength ((app (ps_2) ((cons (d) ((@nil Z))))))) = (m + 1 )) ”
  &&  “ ((m + 1 ) <= 29) ”
  &&  “ (((d + 1 ) * (d + 1 ) ) <= 1000000000000000000) ”
  &&  “ ((d + 1 ) <= n_pre) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (n_pre: Z) (e: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps_2)) = m)) (PreH11 : ((Zlength (es_2)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps_2 es_2 e )),
  (FactorScan n_pre n (d + 1 ) (app (ps_2) ((cons (d) ((@nil Z))))) (app (es_2) ((cons (e) ((@nil Z))))) )
.

Definition solver_entail_wit_4_1_split_goal_2 :=
forall (n_pre: Z) (e: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps_2)) = m)) (PreH11 : ((Zlength (es_2)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps_2 es_2 e )),
  ((Zlength ((app (es_2) ((cons (e) ((@nil Z))))))) = (m + 1 ))
.

Definition solver_entail_wit_4_1_split_goal_3 :=
forall (n_pre: Z) (e: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps_2)) = m)) (PreH11 : ((Zlength (es_2)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps_2 es_2 e )),
  ((Zlength ((app (ps_2) ((cons (d) ((@nil Z))))))) = (m + 1 ))
.

Definition solver_entail_wit_4_1_split_goal_4 :=
forall (n_pre: Z) (e: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps_2)) = m)) (PreH11 : ((Zlength (es_2)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps_2 es_2 e )),
  ((m + 1 ) <= 29)
.

Definition solver_entail_wit_4_1_split_goal_5 :=
forall (n_pre: Z) (e: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps_2)) = m)) (PreH11 : ((Zlength (es_2)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps_2 es_2 e )),
  (((d + 1 ) * (d + 1 ) ) <= 1000000000000000000)
.

Definition solver_entail_wit_4_1_split_goal_6 :=
forall (n_pre: Z) (e: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps_2)) = m)) (PreH11 : ((Zlength (es_2)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps_2 es_2 e )),
  ((d + 1 ) <= n_pre)
.

Definition solver_entail_wit_4_2 :=
(
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (2 <= (d + 1 )) ”
  &&  “ ((d + 1 ) <= n_pre) ”
  &&  “ (((d + 1 ) * (d + 1 ) ) <= 1000000000000000000) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= 29) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (FactorScan n_pre n (d + 1 ) ps es ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
) \/
(
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  TT && emp 
|--
  “ (FactorScan n_pre n (d + 1 ) ps_2 es_2 ) ”
  &&  “ (((d + 1 ) * (d + 1 ) ) <= 1000000000000000000) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  (FactorScan n_pre n (d + 1 ) ps_2 es_2 )
.

Definition solver_entail_wit_4_2_split_goal_2 :=
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  (((d + 1 ) * (d + 1 ) ) <= 1000000000000000000)
.

Definition solver_entail_wit_5_1 :=
(
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n > 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es_2) ((cons (1) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps_2) ((cons (n) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= (m + 1 )) ”
  &&  “ ((m + 1 ) <= 30) ”
  &&  “ ((Zlength (ps)) = (m + 1 )) ”
  &&  “ ((Zlength (es)) = (m + 1 )) ”
  &&  “ (PrimeFactorization n_pre ps es ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
) \/
(
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n > 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  TT && emp 
|--
  “ (PrimeFactorization n_pre (app (ps_2) ((cons (n) ((@nil Z))))) (app (es_2) ((cons (1) ((@nil Z))))) ) ”
  &&  “ ((Zlength ((app (es_2) ((cons (1) ((@nil Z))))))) = (m + 1 )) ”
  &&  “ ((Zlength ((app (ps_2) ((cons (n) ((@nil Z))))))) = (m + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 :=
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n > 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  (PrimeFactorization n_pre (app (ps_2) ((cons (n) ((@nil Z))))) (app (es_2) ((cons (1) ((@nil Z))))) )
.

Definition solver_entail_wit_5_1_split_goal_2 :=
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n > 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  ((Zlength ((app (es_2) ((cons (1) ((@nil Z))))))) = (m + 1 ))
.

Definition solver_entail_wit_5_1_split_goal_3 :=
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n > 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  ((Zlength ((app (ps_2) ((cons (n) ((@nil Z))))))) = (m + 1 ))
.

Definition solver_entail_wit_5_2 :=
(
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n <= 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (PrimeFactorization n_pre ps es ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
) \/
(
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n <= 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  TT && emp 
|--
  “ (PrimeFactorization n_pre ps_2 es_2 ) ”
  &&  “ (1 <= m) ”
  &&  emp
).

Definition solver_entail_wit_5_2_split_goal_1 :=
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n <= 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  (PrimeFactorization n_pre ps_2 es_2 )
.

Definition solver_entail_wit_5_2_split_goal_2 :=
forall (n_pre: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n <= 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps_2)) = m)) (PreH13 : ((Zlength (es_2)) = m)) (PreH14 : (FactorScan n_pre n d ps_2 es_2 )),
  (1 <= m)
.

Definition solver_entail_wit_6 :=
(
forall (n_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (n: Z) (m: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= n)) (PreH4 : (n <= n_pre)) (PreH5 : (1 <= m)) (PreH6 : (m <= 30)) (PreH7 : ((Zlength (ps_2)) = m)) (PreH8 : ((Zlength (es_2)) = m)) (PreH9 : (PrimeFactorization n_pre ps_2 es_2 )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m) ”
  &&  “ (PrefixMaximum es 0 0 ) ”
  &&  “ (PrimeFactorization n_pre ps es ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
) \/
(
forall (n_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (n: Z) (m: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= n)) (PreH4 : (n <= n_pre)) (PreH5 : (1 <= m)) (PreH6 : (m <= 30)) (PreH7 : ((Zlength (ps_2)) = m)) (PreH8 : ((Zlength (es_2)) = m)) (PreH9 : (PrimeFactorization n_pre ps_2 es_2 )),
  TT && emp 
|--
  “ (PrefixMaximum es_2 0 0 ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (n_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (n: Z) (m: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= n)) (PreH4 : (n <= n_pre)) (PreH5 : (1 <= m)) (PreH6 : (m <= 30)) (PreH7 : ((Zlength (ps_2)) = m)) (PreH8 : ((Zlength (es_2)) = m)) (PreH9 : (PrimeFactorization n_pre ps_2 es_2 )),
  (PrefixMaximum es_2 0 0 )
.

Definition solver_entail_wit_7_1 :=
(
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) > maxe)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (0 <= i)) (PreH12 : (i <= m)) (PreH13 : (PrefixMaximum es_2 i maxe )) (PreH14 : (PrimeFactorization n_pre ps_2 es_2 )),
  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m) ”
  &&  “ (PrefixMaximum es (i + 1 ) (Znth (i - 0 ) es_2 0) ) ”
  &&  “ (PrimeFactorization n_pre ps es ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
) \/
(
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) > maxe)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (0 <= i)) (PreH12 : (i <= m)) (PreH13 : (PrefixMaximum es_2 i maxe )) (PreH14 : (PrimeFactorization n_pre ps_2 es_2 )),
  TT && emp 
|--
  “ (PrefixMaximum es_2 (i + 1 ) (Znth (i - 0 ) es_2 0) ) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) > maxe)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (0 <= i)) (PreH12 : (i <= m)) (PreH13 : (PrefixMaximum es_2 i maxe )) (PreH14 : (PrimeFactorization n_pre ps_2 es_2 )),
  (PrefixMaximum es_2 (i + 1 ) (Znth (i - 0 ) es_2 0) )
.

Definition solver_entail_wit_7_2 :=
(
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) <= maxe)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (0 <= i)) (PreH12 : (i <= m)) (PreH13 : (PrefixMaximum es_2 i maxe )) (PreH14 : (PrimeFactorization n_pre ps_2 es_2 )),
  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m) ”
  &&  “ (PrefixMaximum es (i + 1 ) maxe ) ”
  &&  “ (PrimeFactorization n_pre ps es ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
) \/
(
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) <= maxe)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (0 <= i)) (PreH12 : (i <= m)) (PreH13 : (PrefixMaximum es_2 i maxe )) (PreH14 : (PrimeFactorization n_pre ps_2 es_2 )),
  TT && emp 
|--
  “ (PrefixMaximum es_2 (i + 1 ) maxe ) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) <= maxe)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (0 <= i)) (PreH12 : (i <= m)) (PreH13 : (PrefixMaximum es_2 i maxe )) (PreH14 : (PrimeFactorization n_pre ps_2 es_2 )),
  (PrefixMaximum es_2 (i + 1 ) maxe )
.

Definition solver_entail_wit_8 :=
(
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es_2 i maxe )) (PreH13 : (PrimeFactorization n_pre ps_2 es_2 )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (1 <= maxe) ”
  &&  “ (maxe <= 30) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (maxe + 1 )) ”
  &&  “ (MaximumExponent es maxe ) ”
  &&  “ (LayerOptimalityCertificate n_pre ps es maxe ) ”
  &&  “ (LayerSumPrefix n_pre ps es maxe 1 0 ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
) \/
(
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es_2 i maxe )) (PreH13 : (PrimeFactorization n_pre ps_2 es_2 )),
  TT && emp 
|--
  “ (LayerSumPrefix n_pre ps_2 es_2 maxe 1 0 ) ”
  &&  “ (LayerOptimalityCertificate n_pre ps_2 es_2 maxe ) ”
  &&  “ (MaximumExponent es_2 maxe ) ”
  &&  “ (1 <= (maxe + 1 )) ”
  &&  “ (maxe <= 30) ”
  &&  “ (1 <= maxe) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es_2 i maxe )) (PreH13 : (PrimeFactorization n_pre ps_2 es_2 )),
  (LayerSumPrefix n_pre ps_2 es_2 maxe 1 0 )
.

Definition solver_entail_wit_8_split_goal_2 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es_2 i maxe )) (PreH13 : (PrimeFactorization n_pre ps_2 es_2 )),
  (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )
.

Definition solver_entail_wit_8_split_goal_3 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es_2 i maxe )) (PreH13 : (PrimeFactorization n_pre ps_2 es_2 )),
  (MaximumExponent es_2 maxe )
.

Definition solver_entail_wit_8_split_goal_4 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es_2 i maxe )) (PreH13 : (PrimeFactorization n_pre ps_2 es_2 )),
  (1 <= (maxe + 1 ))
.

Definition solver_entail_wit_8_split_goal_5 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es_2 i maxe )) (PreH13 : (PrimeFactorization n_pre ps_2 es_2 )),
  (maxe <= 30)
.

Definition solver_entail_wit_8_split_goal_6 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es_2 i maxe )) (PreH13 : (PrimeFactorization n_pre ps_2 es_2 )),
  (1 <= maxe)
.

Definition solver_entail_wit_9 :=
(
forall (n_pre: Z) (total: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (k <= maxe)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= (maxe + 1 ))) (PreH14 : (MaximumExponent es_2 maxe )) (PreH15 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH16 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (1 <= maxe) ”
  &&  “ (maxe <= 30) ”
  &&  “ (1 <= k) ”
  &&  “ (k <= maxe) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m) ”
  &&  “ (MaximumExponent es maxe ) ”
  &&  “ (LayerOptimalityCertificate n_pre ps es maxe ) ”
  &&  “ (LayerSumPrefix n_pre ps es maxe k total ) ”
  &&  “ (LayerProductPrefix n_pre ps es k 0 1 ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
) \/
(
forall (n_pre: Z) (total: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (k <= maxe)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= (maxe + 1 ))) (PreH14 : (MaximumExponent es_2 maxe )) (PreH15 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH16 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )),
  TT && emp 
|--
  “ (LayerProductPrefix n_pre ps_2 es_2 k 0 1 ) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 :=
forall (n_pre: Z) (total: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (k <= maxe)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= (maxe + 1 ))) (PreH14 : (MaximumExponent es_2 maxe )) (PreH15 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH16 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )),
  (LayerProductPrefix n_pre ps_2 es_2 k 0 1 )
.

Definition solver_entail_wit_10_1 :=
(
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) >= k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es_2 maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH19 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps_2 es_2 k i prod )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (1 <= maxe) ”
  &&  “ (maxe <= 30) ”
  &&  “ (1 <= k) ”
  &&  “ (k <= maxe) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m) ”
  &&  “ (MaximumExponent es maxe ) ”
  &&  “ (LayerOptimalityCertificate n_pre ps es maxe ) ”
  &&  “ (LayerSumPrefix n_pre ps es maxe k total ) ”
  &&  “ (LayerProductPrefix n_pre ps es k (i + 1 ) (prod * (Znth (i - 0 ) ps_2 0) ) ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
) \/
(
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) >= k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es_2 maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH19 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps_2 es_2 k i prod )),
  TT && emp 
|--
  “ (LayerProductPrefix n_pre ps_2 es_2 k (i + 1 ) (prod * (Znth (i - 0 ) ps_2 0) ) ) ”
  &&  emp
).

Definition solver_entail_wit_10_1_split_goal_1 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) >= k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es_2 maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH19 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps_2 es_2 k i prod )),
  (LayerProductPrefix n_pre ps_2 es_2 k (i + 1 ) (prod * (Znth (i - 0 ) ps_2 0) ) )
.

Definition solver_entail_wit_10_2 :=
(
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) < k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es_2 maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH19 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps_2 es_2 k i prod )),
  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (1 <= maxe) ”
  &&  “ (maxe <= 30) ”
  &&  “ (1 <= k) ”
  &&  “ (k <= maxe) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m) ”
  &&  “ (MaximumExponent es maxe ) ”
  &&  “ (LayerOptimalityCertificate n_pre ps es maxe ) ”
  &&  “ (LayerSumPrefix n_pre ps es maxe k total ) ”
  &&  “ (LayerProductPrefix n_pre ps es k (i + 1 ) prod ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
) \/
(
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) < k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es_2 maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH19 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps_2 es_2 k i prod )),
  TT && emp 
|--
  “ (LayerProductPrefix n_pre ps_2 es_2 k (i + 1 ) prod ) ”
  &&  emp
).

Definition solver_entail_wit_10_2_split_goal_1 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es_2 0) < k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps_2)) = m)) (PreH10 : ((Zlength (es_2)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es_2 maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH19 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps_2 es_2 k i prod )),
  (LayerProductPrefix n_pre ps_2 es_2 k (i + 1 ) prod )
.

Definition solver_entail_wit_11 :=
(
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= maxe)) (PreH14 : (0 <= i)) (PreH15 : (i <= m)) (PreH16 : (MaximumExponent es_2 maxe )) (PreH17 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH18 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )) (PreH19 : (LayerProductPrefix n_pre ps_2 es_2 k i prod )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (1 <= maxe) ”
  &&  “ (maxe <= 30) ”
  &&  “ (1 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= (maxe + 1 )) ”
  &&  “ (MaximumExponent es maxe ) ”
  &&  “ (LayerOptimalityCertificate n_pre ps es maxe ) ”
  &&  “ (LayerSumPrefix n_pre ps es maxe (k + 1 ) (total + prod ) ) ”
  &&  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
) \/
(
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= maxe)) (PreH14 : (0 <= i)) (PreH15 : (i <= m)) (PreH16 : (MaximumExponent es_2 maxe )) (PreH17 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH18 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )) (PreH19 : (LayerProductPrefix n_pre ps_2 es_2 k i prod )),
  TT && emp 
|--
  “ (LayerSumPrefix n_pre ps_2 es_2 maxe (k + 1 ) (total + prod ) ) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (i >= m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= maxe)) (PreH14 : (0 <= i)) (PreH15 : (i <= m)) (PreH16 : (MaximumExponent es_2 maxe )) (PreH17 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH18 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )) (PreH19 : (LayerProductPrefix n_pre ps_2 es_2 k i prod )),
  (LayerSumPrefix n_pre ps_2 es_2 maxe (k + 1 ) (total + prod ) )
.

Definition solver_entail_wit_12 :=
(
forall (n_pre: Z) (total: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (k > maxe)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= (maxe + 1 ))) (PreH14 : (MaximumExponent es_2 maxe )) (PreH15 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH16 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (1 <= maxe) ”
  &&  “ (maxe <= 30) ”
  &&  “ (MaximumExponent es maxe ) ”
  &&  “ (LayerOptimalityCertificate n_pre ps es maxe ) ”
  &&  “ (LayerSumPrefix n_pre ps es maxe (maxe + 1 ) total ) ”
  &&  “ (FactorizationAnswer n_pre ps es total ) ”
  &&  (Int64Array.undef_full ( &( "pr" ) ) 40 )
  **  (Int64Array.undef_full ( &( "ex" ) ) 40 )
) \/
(
forall (n_pre: Z) (total: Z) (k: Z) (maxe: Z) (es_2: (@list Z)) (ps_2: (@list Z)) (m: Z) (n: Z) (PreH1 : (k > maxe)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps_2)) = m)) (PreH9 : ((Zlength (es_2)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= (maxe + 1 ))) (PreH14 : (MaximumExponent es_2 maxe )) (PreH15 : (LayerOptimalityCertificate n_pre ps_2 es_2 maxe )) (PreH16 : (LayerSumPrefix n_pre ps_2 es_2 maxe k total )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps_2 )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es_2 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  EX (es: (@list Z)) (ps: (@list Z)),
  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (1 <= maxe) ”
  &&  “ (maxe <= 30) ”
  &&  “ (MaximumExponent es maxe ) ”
  &&  “ (LayerOptimalityCertificate n_pre ps es maxe ) ”
  &&  “ (LayerSumPrefix n_pre ps es maxe (maxe + 1 ) total ) ”
  &&  “ (FactorizationAnswer n_pre ps es total ) ”
  &&  (Int64Array.undef_full ( &( "pr" ) ) 40 )
  **  (Int64Array.undef_full ( &( "ex" ) ) 40 )
).

Definition solver_return_wit_1 :=
(
forall (n_pre: Z) (ps: (@list Z)) (es: (@list Z)) (n: Z) (m: Z) (maxe: Z) (total: Z) (PreH1 : (1 <= n)) (PreH2 : (n <= n_pre)) (PreH3 : (1 <= m)) (PreH4 : (m <= 30)) (PreH5 : ((Zlength (ps)) = m)) (PreH6 : ((Zlength (es)) = m)) (PreH7 : (1 <= maxe)) (PreH8 : (maxe <= 30)) (PreH9 : (MaximumExponent es maxe )) (PreH10 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH11 : (LayerSumPrefix n_pre ps es maxe (maxe + 1 ) total )) (PreH12 : (FactorizationAnswer n_pre ps es total )),
  TT && emp 
|--
  “ (Spec n_pre total ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (ps: (@list Z)) (es: (@list Z)) (n: Z) (m: Z) (maxe: Z) (total: Z) (PreH1 : (1 <= n)) (PreH2 : (n <= n_pre)) (PreH3 : (1 <= m)) (PreH4 : (m <= 30)) (PreH5 : ((Zlength (ps)) = m)) (PreH6 : ((Zlength (es)) = m)) (PreH7 : (1 <= maxe)) (PreH8 : (maxe <= 30)) (PreH9 : (MaximumExponent es maxe )) (PreH10 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH11 : (LayerSumPrefix n_pre ps es maxe (maxe + 1 ) total )) (PreH12 : (FactorizationAnswer n_pre ps es total )),
  TT && emp 
|--
  “ (Spec n_pre total ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (n_pre: Z) (ps: (@list Z)) (es: (@list Z)) (n: Z) (m: Z) (maxe: Z) (total: Z) (PreH1 : (1 <= n)) (PreH2 : (n <= n_pre)) (PreH3 : (1 <= m)) (PreH4 : (m <= 30)) (PreH5 : ((Zlength (ps)) = m)) (PreH6 : ((Zlength (es)) = m)) (PreH7 : (1 <= maxe)) (PreH8 : (maxe <= 30)) (PreH9 : (MaximumExponent es maxe )) (PreH10 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH11 : (LayerSumPrefix n_pre ps es maxe (maxe + 1 ) total )) (PreH12 : (FactorizationAnswer n_pre ps es total )),
  (Spec n_pre total )
.

Definition solver_partial_solve_wit_1 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : ((d * d ) <= n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps)) = m)) (PreH13 : ((Zlength (es)) = m)) (PreH14 : (FactorScan n_pre n d ps es )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((n % ( d ) ) = 0) ”
  &&  “ ((d * d ) <= n) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= n_pre) ”
  &&  “ ((d * d ) <= 1000000000000000000) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= 29) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (FactorScan n_pre n d ps es ) ”
  &&  (((( &( "pr" ) ) + (m * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
.

Definition solver_partial_solve_wit_2 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : ((d * d ) <= n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps)) = m)) (PreH13 : ((Zlength (es)) = m)) (PreH14 : (FactorScan n_pre n d ps es )),
  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((n % ( d ) ) = 0) ”
  &&  “ ((d * d ) <= n) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= n_pre) ”
  &&  “ ((d * d ) <= 1000000000000000000) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= 29) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (FactorScan n_pre n d ps es ) ”
  &&  (((( &( "ex" ) ) + (m * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
.

Definition solver_partial_solve_wit_3 :=
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps)) = m)) (PreH11 : ((Zlength (es)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps es e )),
  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ ((n % ( d ) ) = 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= n_pre) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= 29) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (ExtractionScale n d e ) ”
  &&  “ (FactorExtract n_pre n d ps es e ) ”
  &&  (((( &( "ex" ) ) + (m * sizeof(INT64)))) # Int64  |-> (Znth (m - 0 ) (app (es) ((cons (e) ((@nil Z))))) 0))
  **  (Int64Array.missing_i ( &( "ex" ) ) m 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
.

Definition solver_partial_solve_wit_4 :=
forall (n_pre: Z) (e: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : ((n % ( d ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (2 <= d)) (PreH7 : (d <= n_pre)) (PreH8 : (0 <= m)) (PreH9 : (m <= 29)) (PreH10 : ((Zlength (ps)) = m)) (PreH11 : ((Zlength (es)) = m)) (PreH12 : (ExtractionScale n d e )) (PreH13 : (FactorExtract n_pre n d ps es e )),
  (Int64Array.seg ( &( "ex" ) ) 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
|--
  “ ((n % ( d ) ) = 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= n_pre) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= 29) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (ExtractionScale n d e ) ”
  &&  “ (FactorExtract n_pre n d ps es e ) ”
  &&  (((( &( "ex" ) ) + (m * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i ( &( "ex" ) ) m 0 (m + 1 ) (app (es) ((cons (e) ((@nil Z))))) )
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (d) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
.

Definition solver_partial_solve_wit_5 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n > 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps)) = m)) (PreH13 : ((Zlength (es)) = m)) (PreH14 : (FactorScan n_pre n d ps es )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (n > 1) ”
  &&  “ ((d * d ) > n) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= n_pre) ”
  &&  “ ((d * d ) <= 1000000000000000000) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= 29) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (FactorScan n_pre n d ps es ) ”
  &&  (((( &( "pr" ) ) + (m * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
.

Definition solver_partial_solve_wit_6 :=
forall (n_pre: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (d: Z) (n: Z) (PreH1 : (n > 1)) (PreH2 : ((d * d ) > n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (2 <= d)) (PreH8 : (d <= n_pre)) (PreH9 : ((d * d ) <= 1000000000000000000)) (PreH10 : (0 <= m)) (PreH11 : (m <= 29)) (PreH12 : ((Zlength (ps)) = m)) (PreH13 : ((Zlength (es)) = m)) (PreH14 : (FactorScan n_pre n d ps es )),
  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (n) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (n > 1) ”
  &&  “ ((d * d ) > n) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= n_pre) ”
  &&  “ ((d * d ) <= 1000000000000000000) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= 29) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (FactorScan n_pre n d ps es ) ”
  &&  (((( &( "ex" ) ) + (m * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg ( &( "ex" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "pr" ) ) 0 (m + 1 ) (app (ps) ((cons (n) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pr" ) ) (m + 1 ) 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
.

Definition solver_partial_solve_wit_7 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (i < m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (0 <= i)) (PreH11 : (i <= m)) (PreH12 : (PrefixMaximum es i maxe )) (PreH13 : (PrimeFactorization n_pre ps es )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (i < m) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m) ”
  &&  “ (PrefixMaximum es i maxe ) ”
  &&  “ (PrimeFactorization n_pre ps es ) ”
  &&  (((( &( "ex" ) ) + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) es 0))
  **  (Int64Array.missing_i ( &( "ex" ) ) i 0 m es )
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
.

Definition solver_partial_solve_wit_8 :=
forall (n_pre: Z) (maxe: Z) (i: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es 0) > maxe)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (0 <= i)) (PreH12 : (i <= m)) (PreH13 : (PrefixMaximum es i maxe )) (PreH14 : (PrimeFactorization n_pre ps es )),
  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((Znth (i - 0 ) es 0) > maxe) ”
  &&  “ (i < m) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m) ”
  &&  “ (PrefixMaximum es i maxe ) ”
  &&  “ (PrimeFactorization n_pre ps es ) ”
  &&  (((( &( "ex" ) ) + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) es 0))
  **  (Int64Array.missing_i ( &( "ex" ) ) i 0 m es )
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
.

Definition solver_partial_solve_wit_9 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : (i < m)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= n)) (PreH5 : (n <= n_pre)) (PreH6 : (1 <= m)) (PreH7 : (m <= 30)) (PreH8 : ((Zlength (ps)) = m)) (PreH9 : ((Zlength (es)) = m)) (PreH10 : (1 <= maxe)) (PreH11 : (maxe <= 30)) (PreH12 : (1 <= k)) (PreH13 : (k <= maxe)) (PreH14 : (0 <= i)) (PreH15 : (i <= m)) (PreH16 : (MaximumExponent es maxe )) (PreH17 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH18 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH19 : (LayerProductPrefix n_pre ps es k i prod )),
  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ (i < m) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (1 <= maxe) ”
  &&  “ (maxe <= 30) ”
  &&  “ (1 <= k) ”
  &&  “ (k <= maxe) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m) ”
  &&  “ (MaximumExponent es maxe ) ”
  &&  “ (LayerOptimalityCertificate n_pre ps es maxe ) ”
  &&  “ (LayerSumPrefix n_pre ps es maxe k total ) ”
  &&  “ (LayerProductPrefix n_pre ps es k i prod ) ”
  &&  (((( &( "ex" ) ) + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) es 0))
  **  (Int64Array.missing_i ( &( "ex" ) ) i 0 m es )
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
.

Definition solver_partial_solve_wit_10 :=
forall (n_pre: Z) (prod: Z) (total: Z) (i: Z) (k: Z) (maxe: Z) (es: (@list Z)) (ps: (@list Z)) (m: Z) (n: Z) (PreH1 : ((Znth (i - 0 ) es 0) >= k)) (PreH2 : (i < m)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (1 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (1 <= m)) (PreH8 : (m <= 30)) (PreH9 : ((Zlength (ps)) = m)) (PreH10 : ((Zlength (es)) = m)) (PreH11 : (1 <= maxe)) (PreH12 : (maxe <= 30)) (PreH13 : (1 <= k)) (PreH14 : (k <= maxe)) (PreH15 : (0 <= i)) (PreH16 : (i <= m)) (PreH17 : (MaximumExponent es maxe )) (PreH18 : (LayerOptimalityCertificate n_pre ps es maxe )) (PreH19 : (LayerSumPrefix n_pre ps es maxe k total )) (PreH20 : (LayerProductPrefix n_pre ps es k i prod )),
  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.seg ( &( "pr" ) ) 0 m ps )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
|--
  “ ((Znth (i - 0 ) es 0) >= k) ”
  &&  “ (i < m) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  “ (1 <= m) ”
  &&  “ (m <= 30) ”
  &&  “ ((Zlength (ps)) = m) ”
  &&  “ ((Zlength (es)) = m) ”
  &&  “ (1 <= maxe) ”
  &&  “ (maxe <= 30) ”
  &&  “ (1 <= k) ”
  &&  “ (k <= maxe) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m) ”
  &&  “ (MaximumExponent es maxe ) ”
  &&  “ (LayerOptimalityCertificate n_pre ps es maxe ) ”
  &&  “ (LayerSumPrefix n_pre ps es maxe k total ) ”
  &&  “ (LayerProductPrefix n_pre ps es k i prod ) ”
  &&  (((( &( "pr" ) ) + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) ps 0))
  **  (Int64Array.missing_i ( &( "pr" ) ) i 0 m ps )
  **  (Int64Array.seg ( &( "ex" ) ) 0 m es )
  **  (Int64Array.undef_seg ( &( "pr" ) ) m 40 )
  **  (Int64Array.undef_seg ( &( "ex" ) ) m 40 )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
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

End VC_Correct.
