From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P033_1454D_number_into_sequence_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (n_pre: Z) (out_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)),
  ((( &( "best_exp" ) )) # Int  |->_)
  **  ((( &( "best_prime" ) )) # Int64  |-> n_pre)
  **  ((( &( "value" ) )) # Int64  |-> n_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (n_pre: Z) (out_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)),
  ((( &( "p" ) )) # Int64  |->_)
  **  ((( &( "best_exp" ) )) # Int  |-> 1)
  **  ((( &( "best_prime" ) )) # Int64  |-> n_pre)
  **  ((( &( "value" ) )) # Int64  |-> n_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_3 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (2 <= p)) (PreH6 : (p <= 100001)) (PreH7 : ((p * p ) <= 1000000000000000000)) (PreH8 : (1 <= best_exp)) (PreH9 : (best_exp <= 64)) (PreH10 : (2 <= best_prime)) (PreH11 : (best_prime <= n_pre)) (PreH12 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH13 : (FactorSearchProfile n_pre value p best_prime best_exp ps es )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ ((p * p ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (p * p )) ”
.

Definition solver_safety_wit_4 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((p * p ) <= value)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : ((p * p ) <= 1000000000000000000)) (PreH9 : (1 <= best_exp)) (PreH10 : (best_exp <= 64)) (PreH11 : (2 <= best_prime)) (PreH12 : (best_prime <= n_pre)) (PreH13 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH14 : (FactorSearchProfile n_pre value p best_prime best_exp ps es )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ ((value <> (INT64_MIN)) \/ (p <> (-1))) ”
  &&  “ (p <> 0) ”
.

Definition solver_safety_wit_5 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((p * p ) <= value)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : ((p * p ) <= 1000000000000000000)) (PreH9 : (1 <= best_exp)) (PreH10 : (best_exp <= 64)) (PreH11 : (2 <= best_prime)) (PreH12 : (best_prime <= n_pre)) (PreH13 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH14 : (FactorSearchProfile n_pre value p best_prime best_exp ps es )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) = 0)) (PreH2 : ((p * p ) <= value)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 10000000000)) (PreH5 : (1 <= value)) (PreH6 : (value <= n_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 100001)) (PreH9 : ((p * p ) <= 1000000000000000000)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH15 : (FactorSearchProfile n_pre value p best_prime best_exp ps es )),
  ((( &( "e" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (e: Z) (p: Z) (value: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (2 <= p)) (PreH6 : (p <= 100001)) (PreH7 : (0 <= e)) (PreH8 : (e <= 64)) (PreH9 : (1 <= best_exp)) (PreH10 : (best_exp <= 64)) (PreH11 : (2 <= best_prime)) (PreH12 : (best_prime <= n_pre)) (PreH13 : ((e = 0) -> ((value % ( p ) ) = 0))) (PreH14 : (FactorExtractGuard value p e )) (PreH15 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH16 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps es )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ ((value <> (INT64_MIN)) \/ (p <> (-1))) ”
  &&  “ (p <> 0) ”
.

Definition solver_safety_wit_8 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (e: Z) (p: Z) (value: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (2 <= p)) (PreH6 : (p <= 100001)) (PreH7 : (0 <= e)) (PreH8 : (e <= 64)) (PreH9 : (1 <= best_exp)) (PreH10 : (best_exp <= 64)) (PreH11 : (2 <= best_prime)) (PreH12 : (best_prime <= n_pre)) (PreH13 : ((e = 0) -> ((value % ( p ) ) = 0))) (PreH14 : (FactorExtractGuard value p e )) (PreH15 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH16 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps es )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (e: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (0 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((e = 0) -> ((value % ( p ) ) = 0))) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps es )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ ((value <> (INT64_MIN)) \/ (p <> (-1))) ”
  &&  “ (p <> 0) ”
.

Definition solver_safety_wit_10 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (e: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (0 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((e = 0) -> ((value % ( p ) ) = 0))) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps es )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> (value ÷ p ))
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ ((e + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (e + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (value: Z) (p: Z) (e: Z) (best_exp: Z) (best_prime: Z) (PreH1 : (e > best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (1 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((value % ( p ) ) <> 0)) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps es )) (PreH18 : (FactorExtractProfile n_pre value p e best_prime best_exp ps es )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "best_exp" ) )) # Int  |-> e)
  **  ((( &( "best_prime" ) )) # Int64  |-> p)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ ((p + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_12 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (value: Z) (p: Z) (e: Z) (best_exp: Z) (best_prime: Z) (PreH1 : (e <= best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (1 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((value % ( p ) ) <> 0)) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps es )) (PreH18 : (FactorExtractProfile n_pre value p e best_prime best_exp ps es )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ ((p + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) <> 0)) (PreH2 : ((p * p ) <= value)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 10000000000)) (PreH5 : (1 <= value)) (PreH6 : (value <= n_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 100001)) (PreH9 : ((p * p ) <= 1000000000000000000)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH15 : (FactorSearchProfile n_pre value p best_prime best_exp ps es )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ ((p + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (n_pre: Z) (out_pre: Z) (value: Z) (best_exp: Z) (best_prime: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (BestPowerChoice n_pre best_prime best_exp )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "rest" ) )) # Int64  |-> n_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  (Int64Array.undef_full out_pre 64 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 :=
forall (n_pre: Z) (out_pre: Z) (written: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < best_exp)) (PreH11 : (1 <= rest)) (PreH12 : (rest <= n_pre)) (PreH13 : (BestPowerChoice n_pre best_prime best_exp )) (PreH14 : (OutputPrefixState n_pre best_prime best_exp i rest written )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rest" ) )) # Int64  |-> rest)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (n_pre: Z) (out_pre: Z) (written: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < best_exp)) (PreH11 : (1 <= rest)) (PreH12 : (rest <= n_pre)) (PreH13 : (BestPowerChoice n_pre best_prime best_exp )) (PreH14 : (OutputPrefixState n_pre best_prime best_exp i rest written )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rest" ) )) # Int64  |-> rest)
  **  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i 64 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 :=
forall (n_pre: Z) (out_pre: Z) (written: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : ((i + 1 ) < best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (1 <= best_exp)) (PreH7 : (best_exp <= 64)) (PreH8 : (2 <= best_prime)) (PreH9 : (best_prime <= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < best_exp)) (PreH12 : (1 <= rest)) (PreH13 : (rest <= n_pre)) (PreH14 : (BestPowerChoice n_pre best_prime best_exp )) (PreH15 : (OutputPrefixState n_pre best_prime best_exp i rest written )),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (written) ((cons (best_prime) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) 64 )
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rest" ) )) # Int64  |-> rest)
|--
  “ ((rest <> (INT64_MIN)) \/ (best_prime <> (-1))) ”
  &&  “ (best_prime <> 0) ”
.

Definition solver_safety_wit_18 :=
forall (n_pre: Z) (out_pre: Z) (written: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : ((i + 1 ) < best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (1 <= best_exp)) (PreH7 : (best_exp <= 64)) (PreH8 : (2 <= best_prime)) (PreH9 : (best_prime <= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < best_exp)) (PreH12 : (1 <= rest)) (PreH13 : (rest <= n_pre)) (PreH14 : (BestPowerChoice n_pre best_prime best_exp )) (PreH15 : (OutputPrefixState n_pre best_prime best_exp i rest written )),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (written) ((cons (best_prime) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) 64 )
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rest" ) )) # Int64  |-> (rest ÷ best_prime ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (n_pre: Z) (out_pre: Z) (written: (@list Z)) (value: Z) (best_exp: Z) (best_prime: Z) (rest: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (1 <= rest)) (PreH10 : (rest <= n_pre)) (PreH11 : (BestPowerChoice n_pre best_prime best_exp )) (PreH12 : (OutputPrefixState n_pre best_prime best_exp (best_exp - 1 ) rest written )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  ((( &( "rest" ) )) # Int64  |-> rest)
  **  (Int64Array.seg out_pre 0 (best_exp - 1 ) written )
  **  (Int64Array.undef_seg out_pre (best_exp - 1 ) 64 )
|--
  “ ((best_exp - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (best_exp - 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (n_pre: Z) (out_pre: Z) (written: (@list Z)) (value: Z) (best_exp: Z) (best_prime: Z) (rest: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (1 <= rest)) (PreH10 : (rest <= n_pre)) (PreH11 : (BestPowerChoice n_pre best_prime best_exp )) (PreH12 : (OutputPrefixState n_pre best_prime best_exp (best_exp - 1 ) rest written )),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "value" ) )) # Int64  |-> value)
  **  ((( &( "best_exp" ) )) # Int  |-> best_exp)
  **  ((( &( "best_prime" ) )) # Int64  |-> best_prime)
  **  ((( &( "rest" ) )) # Int64  |-> rest)
  **  (Int64Array.seg out_pre 0 (best_exp - 1 ) written )
  **  (Int64Array.undef_seg out_pre (best_exp - 1 ) 64 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (n_pre: Z) (out_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)),
  (Int64Array.undef_full out_pre 64 )
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= 100001) ”
  &&  “ ((2 * 2 ) <= 1000000000000000000) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= 64) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (FactorSearchState n_pre n_pre 2 n_pre 1 ) ”
  &&  “ (FactorSearchProfile n_pre n_pre 2 n_pre 1 ps es ) ”
  &&  (Int64Array.undef_full out_pre 64 )
) \/
(
forall (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)),
  TT && emp 
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= 100001) ”
  &&  “ ((2 * 2 ) <= 1000000000000000000) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= 64) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (FactorSearchState n_pre n_pre 2 n_pre 1 ) ”
  &&  “ (FactorSearchProfile n_pre n_pre 2 n_pre 1 ps es ) ”
  &&  emp
).

Definition solver_entail_wit_2 :=
(
forall (n_pre: Z) (out_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) = 0)) (PreH2 : ((p * p ) <= value)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 10000000000)) (PreH5 : (1 <= value)) (PreH6 : (value <= n_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 100001)) (PreH9 : ((p * p ) <= 1000000000000000000)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH15 : (FactorSearchProfile n_pre value p best_prime best_exp ps_2 es_2 )),
  (Int64Array.undef_full out_pre 64 )
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 100001) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 64) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ ((0 = 0) -> ((value % ( p ) ) = 0)) ”
  &&  “ (FactorExtractGuard value p 0 ) ”
  &&  “ (FactorExtractState n_pre value p 0 best_prime best_exp ) ”
  &&  “ (FactorExtractOrigin n_pre value p 0 best_prime best_exp ps es ) ”
  &&  (Int64Array.undef_full out_pre 64 )
) \/
(
forall (n_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) = 0)) (PreH2 : ((p * p ) <= value)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 10000000000)) (PreH5 : (1 <= value)) (PreH6 : (value <= n_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 100001)) (PreH9 : ((p * p ) <= 1000000000000000000)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH15 : (FactorSearchProfile n_pre value p best_prime best_exp ps_2 es_2 )),
  TT && emp 
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (0 <= 0) ”
  &&  “ (0 <= 64) ”
  &&  “ ((0 = 0) -> ((value % ( p ) ) = 0)) ”
  &&  “ (FactorExtractGuard value p 0 ) ”
  &&  “ (FactorExtractState n_pre value p 0 best_prime best_exp ) ”
  &&  “ (FactorExtractOrigin n_pre value p 0 best_prime best_exp ps es ) ”
  &&  emp
).

Definition solver_entail_wit_3 :=
(
forall (n_pre: Z) (out_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (best_prime: Z) (best_exp: Z) (e: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (0 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((e = 0) -> ((value % ( p ) ) = 0))) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps_2 es_2 )),
  (Int64Array.undef_full out_pre 64 )
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= (value ÷ p )) ”
  &&  “ ((value ÷ p ) <= n_pre) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 100001) ”
  &&  “ (0 <= (e + 1 )) ”
  &&  “ ((e + 1 ) <= 64) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ (((e + 1 ) = 0) -> (((value ÷ p ) % ( p ) ) = 0)) ”
  &&  “ (FactorExtractGuard (value ÷ p ) p (e + 1 ) ) ”
  &&  “ (FactorExtractState n_pre (value ÷ p ) p (e + 1 ) best_prime best_exp ) ”
  &&  “ (FactorExtractOrigin n_pre (value ÷ p ) p (e + 1 ) best_prime best_exp ps es ) ”
  &&  (Int64Array.undef_full out_pre 64 )
) \/
(
forall (n_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (best_prime: Z) (best_exp: Z) (e: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (0 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((e = 0) -> ((value % ( p ) ) = 0))) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps_2 es_2 )),
  TT && emp 
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (1 <= (value ÷ p )) ”
  &&  “ ((value ÷ p ) <= n_pre) ”
  &&  “ (0 <= (e + 1 )) ”
  &&  “ ((e + 1 ) <= 64) ”
  &&  “ (((e + 1 ) = 0) -> (((value ÷ p ) % ( p ) ) = 0)) ”
  &&  “ (FactorExtractGuard (value ÷ p ) p (e + 1 ) ) ”
  &&  “ (FactorExtractState n_pre (value ÷ p ) p (e + 1 ) best_prime best_exp ) ”
  &&  “ (FactorExtractOrigin n_pre (value ÷ p ) p (e + 1 ) best_prime best_exp ps es ) ”
  &&  emp
).

Definition solver_entail_wit_4 :=
(
forall (n_pre: Z) (out_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (best_prime: Z) (best_exp: Z) (e: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (0 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((e = 0) -> ((value % ( p ) ) = 0))) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps_2 es_2 )),
  (Int64Array.undef_full out_pre 64 )
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 100001) ”
  &&  “ (1 <= e) ”
  &&  “ (e <= 64) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ ((value % ( p ) ) <> 0) ”
  &&  “ (FactorExtractGuard value p e ) ”
  &&  “ (FactorExtractState n_pre value p e best_prime best_exp ) ”
  &&  “ (FactorExtractOrigin n_pre value p e best_prime best_exp ps es ) ”
  &&  “ (FactorExtractProfile n_pre value p e best_prime best_exp ps es ) ”
  &&  (Int64Array.undef_full out_pre 64 )
) \/
(
forall (n_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (best_prime: Z) (best_exp: Z) (e: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (0 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((e = 0) -> ((value % ( p ) ) = 0))) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps_2 es_2 )),
  TT && emp 
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (1 <= e) ”
  &&  “ (FactorExtractOrigin n_pre value p e best_prime best_exp ps es ) ”
  &&  “ (FactorExtractProfile n_pre value p e best_prime best_exp ps es ) ”
  &&  emp
).

Definition solver_entail_wit_5 :=
(
forall (n_pre: Z) (out_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((p * p ) > value)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : ((p * p ) <= 1000000000000000000)) (PreH9 : (1 <= best_exp)) (PreH10 : (best_exp <= 64)) (PreH11 : (2 <= best_prime)) (PreH12 : (best_prime <= n_pre)) (PreH13 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH14 : (FactorSearchProfile n_pre value p best_prime best_exp ps es )),
  (Int64Array.undef_full out_pre 64 )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ (BestPowerChoice n_pre best_prime best_exp ) ”
  &&  (Int64Array.undef_full out_pre 64 )
) \/
(
forall (n_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((p * p ) > value)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : ((p * p ) <= 1000000000000000000)) (PreH9 : (1 <= best_exp)) (PreH10 : (best_exp <= 64)) (PreH11 : (2 <= best_prime)) (PreH12 : (best_prime <= n_pre)) (PreH13 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH14 : (FactorSearchProfile n_pre value p best_prime best_exp ps es )),
  TT && emp 
|--
  “ (BestPowerChoice n_pre best_prime best_exp ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (n_pre: Z) (ps: (@list Z)) (es: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((p * p ) > value)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : ((p * p ) <= 1000000000000000000)) (PreH9 : (1 <= best_exp)) (PreH10 : (best_exp <= 64)) (PreH11 : (2 <= best_prime)) (PreH12 : (best_prime <= n_pre)) (PreH13 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH14 : (FactorSearchProfile n_pre value p best_prime best_exp ps es )),
  (BestPowerChoice n_pre best_prime best_exp )
.

Definition solver_entail_wit_6_1 :=
(
forall (n_pre: Z) (out_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (value: Z) (p: Z) (e: Z) (best_exp: Z) (best_prime: Z) (PreH1 : (e > best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (1 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((value % ( p ) ) <> 0)) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps_2 es_2 )) (PreH18 : (FactorExtractProfile n_pre value p e best_prime best_exp ps_2 es_2 )),
  (Int64Array.undef_full out_pre 64 )
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (2 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= 100001) ”
  &&  “ (((p + 1 ) * (p + 1 ) ) <= 1000000000000000000) ”
  &&  “ (1 <= e) ”
  &&  “ (e <= 64) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= n_pre) ”
  &&  “ (FactorSearchState n_pre value (p + 1 ) p e ) ”
  &&  “ (FactorSearchProfile n_pre value (p + 1 ) p e ps es ) ”
  &&  (Int64Array.undef_full out_pre 64 )
) \/
(
forall (n_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (value: Z) (p: Z) (e: Z) (best_exp: Z) (best_prime: Z) (PreH1 : (e > best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (1 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((value % ( p ) ) <> 0)) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps_2 es_2 )) (PreH18 : (FactorExtractProfile n_pre value p e best_prime best_exp ps_2 es_2 )),
  TT && emp 
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (2 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= 100001) ”
  &&  “ (((p + 1 ) * (p + 1 ) ) <= 1000000000000000000) ”
  &&  “ (p <= n_pre) ”
  &&  “ (FactorSearchState n_pre value (p + 1 ) p e ) ”
  &&  “ (FactorSearchProfile n_pre value (p + 1 ) p e ps es ) ”
  &&  emp
).

Definition solver_entail_wit_6_2 :=
(
forall (n_pre: Z) (out_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (value: Z) (p: Z) (e: Z) (best_exp: Z) (best_prime: Z) (PreH1 : (e <= best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (1 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((value % ( p ) ) <> 0)) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps_2 es_2 )) (PreH18 : (FactorExtractProfile n_pre value p e best_prime best_exp ps_2 es_2 )),
  (Int64Array.undef_full out_pre 64 )
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (2 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= 100001) ”
  &&  “ (((p + 1 ) * (p + 1 ) ) <= 1000000000000000000) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ (FactorSearchState n_pre value (p + 1 ) best_prime best_exp ) ”
  &&  “ (FactorSearchProfile n_pre value (p + 1 ) best_prime best_exp ps es ) ”
  &&  (Int64Array.undef_full out_pre 64 )
) \/
(
forall (n_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (value: Z) (p: Z) (e: Z) (best_exp: Z) (best_prime: Z) (PreH1 : (e <= best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 100001)) (PreH8 : (1 <= e)) (PreH9 : (e <= 64)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : ((value % ( p ) ) <> 0)) (PreH15 : (FactorExtractGuard value p e )) (PreH16 : (FactorExtractState n_pre value p e best_prime best_exp )) (PreH17 : (FactorExtractOrigin n_pre value p e best_prime best_exp ps_2 es_2 )) (PreH18 : (FactorExtractProfile n_pre value p e best_prime best_exp ps_2 es_2 )),
  TT && emp 
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (2 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= 100001) ”
  &&  “ (((p + 1 ) * (p + 1 ) ) <= 1000000000000000000) ”
  &&  “ (FactorSearchState n_pre value (p + 1 ) best_prime best_exp ) ”
  &&  “ (FactorSearchProfile n_pre value (p + 1 ) best_prime best_exp ps es ) ”
  &&  emp
).

Definition solver_entail_wit_6_3 :=
(
forall (n_pre: Z) (out_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) <> 0)) (PreH2 : ((p * p ) <= value)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 10000000000)) (PreH5 : (1 <= value)) (PreH6 : (value <= n_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 100001)) (PreH9 : ((p * p ) <= 1000000000000000000)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH15 : (FactorSearchProfile n_pre value p best_prime best_exp ps_2 es_2 )),
  (Int64Array.undef_full out_pre 64 )
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (2 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= 100001) ”
  &&  “ (((p + 1 ) * (p + 1 ) ) <= 1000000000000000000) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ (FactorSearchState n_pre value (p + 1 ) best_prime best_exp ) ”
  &&  “ (FactorSearchProfile n_pre value (p + 1 ) best_prime best_exp ps es ) ”
  &&  (Int64Array.undef_full out_pre 64 )
) \/
(
forall (n_pre: Z) (ps_2: (@list Z)) (es_2: (@list Z)) (best_prime: Z) (best_exp: Z) (p: Z) (value: Z) (PreH1 : ((value % ( p ) ) <> 0)) (PreH2 : ((p * p ) <= value)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 10000000000)) (PreH5 : (1 <= value)) (PreH6 : (value <= n_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 100001)) (PreH9 : ((p * p ) <= 1000000000000000000)) (PreH10 : (1 <= best_exp)) (PreH11 : (best_exp <= 64)) (PreH12 : (2 <= best_prime)) (PreH13 : (best_prime <= n_pre)) (PreH14 : (FactorSearchState n_pre value p best_prime best_exp )) (PreH15 : (FactorSearchProfile n_pre value p best_prime best_exp ps_2 es_2 )),
  TT && emp 
|--
  EX (ps: (@list Z)) (es: (@list Z)),
  “ (2 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= 100001) ”
  &&  “ (((p + 1 ) * (p + 1 ) ) <= 1000000000000000000) ”
  &&  “ (FactorSearchState n_pre value (p + 1 ) best_prime best_exp ) ”
  &&  “ (FactorSearchProfile n_pre value (p + 1 ) best_prime best_exp ps es ) ”
  &&  emp
).

Definition solver_entail_wit_7 :=
(
forall (n_pre: Z) (out_pre: Z) (value: Z) (best_exp: Z) (best_prime: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (BestPowerChoice n_pre best_prime best_exp )),
  (Int64Array.undef_full out_pre 64 )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < best_exp) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (BestPowerChoice n_pre best_prime best_exp ) ”
  &&  “ (OutputPrefixState n_pre best_prime best_exp 0 n_pre written ) ”
  &&  (Int64Array.seg out_pre 0 0 written )
  **  (Int64Array.undef_seg out_pre 0 64 )
) \/
(
forall (n_pre: Z) (value: Z) (best_exp: Z) (best_prime: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (BestPowerChoice n_pre best_prime best_exp )),
  TT && emp 
|--
  “ (OutputPrefixState n_pre best_prime best_exp 0 n_pre (@nil Z) ) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (n_pre: Z) (value: Z) (best_exp: Z) (best_prime: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (BestPowerChoice n_pre best_prime best_exp )),
  (OutputPrefixState n_pre best_prime best_exp 0 n_pre (@nil Z) )
.

Definition solver_entail_wit_8 :=
(
forall (n_pre: Z) (out_pre: Z) (written_2: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : ((i + 1 ) < best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (1 <= best_exp)) (PreH7 : (best_exp <= 64)) (PreH8 : (2 <= best_prime)) (PreH9 : (best_prime <= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < best_exp)) (PreH12 : (1 <= rest)) (PreH13 : (rest <= n_pre)) (PreH14 : (BestPowerChoice n_pre best_prime best_exp )) (PreH15 : (OutputPrefixState n_pre best_prime best_exp i rest written_2 )),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (written_2) ((cons (best_prime) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) 64 )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) < best_exp) ”
  &&  “ (1 <= (rest ÷ best_prime )) ”
  &&  “ ((rest ÷ best_prime ) <= n_pre) ”
  &&  “ (BestPowerChoice n_pre best_prime best_exp ) ”
  &&  “ (OutputPrefixState n_pre best_prime best_exp (i + 1 ) (rest ÷ best_prime ) written ) ”
  &&  (Int64Array.seg out_pre 0 (i + 1 ) written )
  **  (Int64Array.undef_seg out_pre (i + 1 ) 64 )
) \/
(
forall (n_pre: Z) (written_2: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : ((i + 1 ) < best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (1 <= best_exp)) (PreH7 : (best_exp <= 64)) (PreH8 : (2 <= best_prime)) (PreH9 : (best_prime <= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < best_exp)) (PreH12 : (1 <= rest)) (PreH13 : (rest <= n_pre)) (PreH14 : (BestPowerChoice n_pre best_prime best_exp )) (PreH15 : (OutputPrefixState n_pre best_prime best_exp i rest written_2 )),
  TT && emp 
|--
  “ (OutputPrefixState n_pre best_prime best_exp (i + 1 ) (rest ÷ best_prime ) (app (written_2) ((cons (best_prime) ((@nil Z))))) ) ”
  &&  “ ((rest ÷ best_prime ) <= n_pre) ”
  &&  “ (1 <= (rest ÷ best_prime )) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 :=
forall (n_pre: Z) (written_2: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : ((i + 1 ) < best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (1 <= best_exp)) (PreH7 : (best_exp <= 64)) (PreH8 : (2 <= best_prime)) (PreH9 : (best_prime <= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < best_exp)) (PreH12 : (1 <= rest)) (PreH13 : (rest <= n_pre)) (PreH14 : (BestPowerChoice n_pre best_prime best_exp )) (PreH15 : (OutputPrefixState n_pre best_prime best_exp i rest written_2 )),
  (OutputPrefixState n_pre best_prime best_exp (i + 1 ) (rest ÷ best_prime ) (app (written_2) ((cons (best_prime) ((@nil Z))))) )
.

Definition solver_entail_wit_8_split_goal_2 :=
forall (n_pre: Z) (written_2: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : ((i + 1 ) < best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (1 <= best_exp)) (PreH7 : (best_exp <= 64)) (PreH8 : (2 <= best_prime)) (PreH9 : (best_prime <= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < best_exp)) (PreH12 : (1 <= rest)) (PreH13 : (rest <= n_pre)) (PreH14 : (BestPowerChoice n_pre best_prime best_exp )) (PreH15 : (OutputPrefixState n_pre best_prime best_exp i rest written_2 )),
  ((rest ÷ best_prime ) <= n_pre)
.

Definition solver_entail_wit_8_split_goal_3 :=
forall (n_pre: Z) (written_2: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : ((i + 1 ) < best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (1 <= best_exp)) (PreH7 : (best_exp <= 64)) (PreH8 : (2 <= best_prime)) (PreH9 : (best_prime <= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < best_exp)) (PreH12 : (1 <= rest)) (PreH13 : (rest <= n_pre)) (PreH14 : (BestPowerChoice n_pre best_prime best_exp )) (PreH15 : (OutputPrefixState n_pre best_prime best_exp i rest written_2 )),
  (1 <= (rest ÷ best_prime ))
.

Definition solver_entail_wit_9 :=
(
forall (n_pre: Z) (out_pre: Z) (written_2: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : ((i + 1 ) >= best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (1 <= best_exp)) (PreH7 : (best_exp <= 64)) (PreH8 : (2 <= best_prime)) (PreH9 : (best_prime <= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < best_exp)) (PreH12 : (1 <= rest)) (PreH13 : (rest <= n_pre)) (PreH14 : (BestPowerChoice n_pre best_prime best_exp )) (PreH15 : (OutputPrefixState n_pre best_prime best_exp i rest written_2 )),
  (Int64Array.seg out_pre 0 i written_2 )
  **  (Int64Array.undef_seg out_pre i 64 )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ (1 <= rest) ”
  &&  “ (rest <= n_pre) ”
  &&  “ (BestPowerChoice n_pre best_prime best_exp ) ”
  &&  “ (OutputPrefixState n_pre best_prime best_exp (best_exp - 1 ) rest written ) ”
  &&  (Int64Array.seg out_pre 0 (best_exp - 1 ) written )
  **  (Int64Array.undef_seg out_pre (best_exp - 1 ) 64 )
) \/
(
forall (n_pre: Z) (out_pre: Z) (written_2: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : ((i + 1 ) >= best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (1 <= best_exp)) (PreH7 : (best_exp <= 64)) (PreH8 : (2 <= best_prime)) (PreH9 : (best_prime <= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < best_exp)) (PreH12 : (1 <= rest)) (PreH13 : (rest <= n_pre)) (PreH14 : (BestPowerChoice n_pre best_prime best_exp )) (PreH15 : (OutputPrefixState n_pre best_prime best_exp i rest written_2 )),
  (Int64Array.seg out_pre 0 i written_2 )
|--
  EX (written: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ (1 <= rest) ”
  &&  “ (rest <= n_pre) ”
  &&  “ (BestPowerChoice n_pre best_prime best_exp ) ”
  &&  “ (OutputPrefixState n_pre best_prime best_exp (best_exp - 1 ) rest written ) ”
  &&  (Int64Array.seg out_pre 0 (best_exp - 1 ) written )
).

Definition solver_entail_wit_10 :=
(
forall (n_pre: Z) (out_pre: Z) (written: (@list Z)) (value: Z) (best_exp: Z) (best_prime: Z) (rest: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (1 <= rest)) (PreH10 : (rest <= n_pre)) (PreH11 : (BestPowerChoice n_pre best_prime best_exp )) (PreH12 : (OutputPrefixState n_pre best_prime best_exp (best_exp - 1 ) rest written )),
  (Int64Array.seg out_pre 0 ((best_exp - 1 ) + 1 ) (app (written) ((cons (rest) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre ((best_exp - 1 ) + 1 ) 64 )
|--
  EX (result: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (FinalOutputSequence n_pre best_prime best_exp rest result ) ”
  &&  “ (Spec n_pre result ) ”
  &&  (Int64Array.full out_pre best_exp result )
  **  (Int64Array.undef_seg out_pre best_exp 64 )
) \/
(
forall (n_pre: Z) (written: (@list Z)) (value: Z) (best_exp: Z) (best_prime: Z) (rest: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (1 <= rest)) (PreH10 : (rest <= n_pre)) (PreH11 : (BestPowerChoice n_pre best_prime best_exp )) (PreH12 : (OutputPrefixState n_pre best_prime best_exp (best_exp - 1 ) rest written )),
  TT && emp 
|--
  “ (Spec n_pre (app (written) ((cons (rest) ((@nil Z))))) ) ”
  &&  “ (FinalOutputSequence n_pre best_prime best_exp rest (app (written) ((cons (rest) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_10_split_goal_1 :=
forall (n_pre: Z) (written: (@list Z)) (value: Z) (best_exp: Z) (best_prime: Z) (rest: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (1 <= rest)) (PreH10 : (rest <= n_pre)) (PreH11 : (BestPowerChoice n_pre best_prime best_exp )) (PreH12 : (OutputPrefixState n_pre best_prime best_exp (best_exp - 1 ) rest written )),
  (Spec n_pre (app (written) ((cons (rest) ((@nil Z))))) )
.

Definition solver_entail_wit_10_split_goal_2 :=
forall (n_pre: Z) (written: (@list Z)) (value: Z) (best_exp: Z) (best_prime: Z) (rest: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (1 <= rest)) (PreH10 : (rest <= n_pre)) (PreH11 : (BestPowerChoice n_pre best_prime best_exp )) (PreH12 : (OutputPrefixState n_pre best_prime best_exp (best_exp - 1 ) rest written )),
  (FinalOutputSequence n_pre best_prime best_exp rest (app (written) ((cons (rest) ((@nil Z))))) )
.

Definition solver_return_wit_1 :=
(
forall (n_pre: Z) (out_pre: Z) (result_2: (@list Z)) (value: Z) (best_exp: Z) (rest: Z) (best_prime: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (FinalOutputSequence n_pre best_prime best_exp rest result_2 )) (PreH8 : (Spec n_pre result_2 )),
  (Int64Array.full out_pre best_exp result_2 )
  **  (Int64Array.undef_seg out_pre best_exp 64 )
|--
  EX (result: (@list Z)),
  “ (Spec n_pre result ) ”
  &&  “ (best_exp = (Zlength (result))) ”
  &&  (Int64Array.full out_pre best_exp result )
  **  (Int64Array.undef_seg out_pre best_exp 64 )
) \/
(
forall (n_pre: Z) (result_2: (@list Z)) (value: Z) (best_exp: Z) (rest: Z) (best_prime: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (FinalOutputSequence n_pre best_prime best_exp rest result_2 )) (PreH8 : (Spec n_pre result_2 )),
  TT && emp 
|--
  “ (best_exp = (Zlength (result_2))) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (n_pre: Z) (result_2: (@list Z)) (value: Z) (best_exp: Z) (rest: Z) (best_prime: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (FinalOutputSequence n_pre best_prime best_exp rest result_2 )) (PreH8 : (Spec n_pre result_2 )),
  (best_exp = (Zlength (result_2)))
.

Definition solver_partial_solve_wit_1 :=
forall (n_pre: Z) (out_pre: Z) (written: (@list Z)) (rest: Z) (i: Z) (best_prime: Z) (best_exp: Z) (value: Z) (PreH1 : ((i + 1 ) < best_exp)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 10000000000)) (PreH4 : (1 <= value)) (PreH5 : (value <= n_pre)) (PreH6 : (1 <= best_exp)) (PreH7 : (best_exp <= 64)) (PreH8 : (2 <= best_prime)) (PreH9 : (best_prime <= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < best_exp)) (PreH12 : (1 <= rest)) (PreH13 : (rest <= n_pre)) (PreH14 : (BestPowerChoice n_pre best_prime best_exp )) (PreH15 : (OutputPrefixState n_pre best_prime best_exp i rest written )),
  (Int64Array.seg out_pre 0 i written )
  **  (Int64Array.undef_seg out_pre i 64 )
|--
  “ ((i + 1 ) < best_exp) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < best_exp) ”
  &&  “ (1 <= rest) ”
  &&  “ (rest <= n_pre) ”
  &&  “ (BestPowerChoice n_pre best_prime best_exp ) ”
  &&  “ (OutputPrefixState n_pre best_prime best_exp i rest written ) ”
  &&  (((out_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg out_pre (i + 1 ) 64 )
  **  (Int64Array.seg out_pre 0 i written )
.

Definition solver_partial_solve_wit_2 :=
forall (n_pre: Z) (out_pre: Z) (written: (@list Z)) (value: Z) (best_exp: Z) (best_prime: Z) (rest: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 10000000000)) (PreH3 : (1 <= value)) (PreH4 : (value <= n_pre)) (PreH5 : (1 <= best_exp)) (PreH6 : (best_exp <= 64)) (PreH7 : (2 <= best_prime)) (PreH8 : (best_prime <= n_pre)) (PreH9 : (1 <= rest)) (PreH10 : (rest <= n_pre)) (PreH11 : (BestPowerChoice n_pre best_prime best_exp )) (PreH12 : (OutputPrefixState n_pre best_prime best_exp (best_exp - 1 ) rest written )),
  (Int64Array.seg out_pre 0 (best_exp - 1 ) written )
  **  (Int64Array.undef_seg out_pre (best_exp - 1 ) 64 )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 10000000000) ”
  &&  “ (1 <= value) ”
  &&  “ (value <= n_pre) ”
  &&  “ (1 <= best_exp) ”
  &&  “ (best_exp <= 64) ”
  &&  “ (2 <= best_prime) ”
  &&  “ (best_prime <= n_pre) ”
  &&  “ (1 <= rest) ”
  &&  “ (rest <= n_pre) ”
  &&  “ (BestPowerChoice n_pre best_prime best_exp ) ”
  &&  “ (OutputPrefixState n_pre best_prime best_exp (best_exp - 1 ) rest written ) ”
  &&  (((out_pre + ((best_exp - 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg out_pre ((best_exp - 1 ) + 1 ) 64 )
  **  (Int64Array.seg out_pre 0 (best_exp - 1 ) written )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_entail_wit_6_3 : solver_entail_wit_6_3.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
