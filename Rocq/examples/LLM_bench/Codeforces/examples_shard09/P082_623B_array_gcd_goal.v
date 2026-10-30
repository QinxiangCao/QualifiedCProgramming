From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P082_623B_array_gcd_lib.
Local Open Scope sac.

(*----- Function add_factors -----*)

Definition add_factors_safety_wit_1 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (v_pre: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (PreH1 : ((Zlength (all)) = 256)) (PreH2 : ((sublist (0) (k0) (all)) = pre)) (PreH3 : (v_pre = v0)) (PreH4 : (1 <= v0)) (PreH5 : (v0 <= 1000000001)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)),
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  (Int64Array.full primes_pre 256 all )
  **  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((nprime_pre) # Int  |-> k0)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_factors_safety_wit_2 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : (1 <= v0)) (PreH2 : (v0 <= 1000000001)) (PreH3 : (1 <= v)) (PreH4 : (v <= v0)) (PreH5 : (2 <= d)) (PreH6 : (d <= 31624)) (PreH7 : (0 <= k0)) (PreH8 : (k0 <= 200)) (PreH9 : ((Zlength (pre)) = k0)) (PreH10 : (0 <= (Zlength (fs)))) (PreH11 : ((Zlength (fs)) <= 29)) (PreH12 : ((Zlength (all)) = 256)) (PreH13 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH14 : (AddFactorsScan v0 v d fs )),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ ((d * d ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (d * d )) ”
.

Definition add_factors_safety_wit_3 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : ((d * d ) <= v)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : (0 <= k0)) (PreH9 : (k0 <= 200)) (PreH10 : ((Zlength (pre)) = k0)) (PreH11 : (0 <= (Zlength (fs)))) (PreH12 : ((Zlength (fs)) <= 29)) (PreH13 : ((Zlength (all)) = 256)) (PreH14 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH15 : (AddFactorsScan v0 v d fs )),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ ((v <> (INT64_MIN)) \/ (d <> (-1))) ”
  &&  “ (d <> 0) ”
.

Definition add_factors_safety_wit_4 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : ((d * d ) <= v)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : (0 <= k0)) (PreH9 : (k0 <= 200)) (PreH10 : ((Zlength (pre)) = k0)) (PreH11 : (0 <= (Zlength (fs)))) (PreH12 : ((Zlength (fs)) <= 29)) (PreH13 : ((Zlength (all)) = 256)) (PreH14 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH15 : (AddFactorsScan v0 v d fs )),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_factors_safety_wit_5 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) = 0)) (PreH2 : ((d * d ) <= v)) (PreH3 : (1 <= v0)) (PreH4 : (v0 <= 1000000001)) (PreH5 : (1 <= v)) (PreH6 : (v <= v0)) (PreH7 : (2 <= d)) (PreH8 : (d <= 31624)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (0 <= (Zlength (fs)))) (PreH13 : ((Zlength (fs)) <= 29)) (PreH14 : ((Zlength (all)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH16 : (AddFactorsScan v0 v d fs )),
  (Int64Array.full primes_pre 256 (replace_Znth ((k0 + (Zlength (fs)) )) (d) (all)) )
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
|--
  “ (((k0 + (Zlength (fs)) ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((k0 + (Zlength (fs)) ) + 1 )) ”
.

Definition add_factors_safety_wit_6 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : (1 <= v0)) (PreH2 : (v0 <= 1000000001)) (PreH3 : (1 <= v)) (PreH4 : (v <= v0)) (PreH5 : (2 <= d)) (PreH6 : (d <= 31624)) (PreH7 : ((d * d ) <= v0)) (PreH8 : (0 <= k0)) (PreH9 : (k0 <= 200)) (PreH10 : ((Zlength (pre)) = k0)) (PreH11 : (1 <= (Zlength (fs)))) (PreH12 : ((Zlength (fs)) <= 30)) (PreH13 : ((Zlength (all)) = 256)) (PreH14 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH15 : (AddFactorsExtract v0 v d fs )) (PreH16 : (AddFactorsScan v0 v d fs )),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ ((v <> (INT64_MIN)) \/ (d <> (-1))) ”
  &&  “ (d <> 0) ”
.

Definition add_factors_safety_wit_7 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : (1 <= v0)) (PreH2 : (v0 <= 1000000001)) (PreH3 : (1 <= v)) (PreH4 : (v <= v0)) (PreH5 : (2 <= d)) (PreH6 : (d <= 31624)) (PreH7 : ((d * d ) <= v0)) (PreH8 : (0 <= k0)) (PreH9 : (k0 <= 200)) (PreH10 : ((Zlength (pre)) = k0)) (PreH11 : (1 <= (Zlength (fs)))) (PreH12 : ((Zlength (fs)) <= 30)) (PreH13 : ((Zlength (all)) = 256)) (PreH14 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH15 : (AddFactorsExtract v0 v d fs )) (PreH16 : ((v % ( d ) ) = 0)),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ ((v <> (INT64_MIN)) \/ (d <> (-1))) ”
  &&  “ (d <> 0) ”
.

Definition add_factors_safety_wit_8 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : (1 <= v0)) (PreH2 : (v0 <= 1000000001)) (PreH3 : (1 <= v)) (PreH4 : (v <= v0)) (PreH5 : (2 <= d)) (PreH6 : (d <= 31624)) (PreH7 : ((d * d ) <= v0)) (PreH8 : (0 <= k0)) (PreH9 : (k0 <= 200)) (PreH10 : ((Zlength (pre)) = k0)) (PreH11 : (1 <= (Zlength (fs)))) (PreH12 : ((Zlength (fs)) <= 30)) (PreH13 : ((Zlength (all)) = 256)) (PreH14 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH15 : (AddFactorsExtract v0 v d fs )) (PreH16 : ((v % ( d ) ) = 0)),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_factors_safety_wit_9 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : (1 <= v0)) (PreH2 : (v0 <= 1000000001)) (PreH3 : (1 <= v)) (PreH4 : (v <= v0)) (PreH5 : (2 <= d)) (PreH6 : (d <= 31624)) (PreH7 : ((d * d ) <= v0)) (PreH8 : (0 <= k0)) (PreH9 : (k0 <= 200)) (PreH10 : ((Zlength (pre)) = k0)) (PreH11 : (1 <= (Zlength (fs)))) (PreH12 : ((Zlength (fs)) <= 30)) (PreH13 : ((Zlength (all)) = 256)) (PreH14 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH15 : (AddFactorsExtract v0 v d fs )) (PreH16 : (AddFactorsScan v0 v d fs )),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_factors_safety_wit_10 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) <> 0)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : ((d * d ) <= v0)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (1 <= (Zlength (fs)))) (PreH13 : ((Zlength (fs)) <= 30)) (PreH14 : ((Zlength (all)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH16 : (AddFactorsExtract v0 v d fs )) (PreH17 : ((v % ( d ) ) = 0)),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ False ”
.

Definition add_factors_safety_wit_11 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) = 0)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : ((d * d ) <= v0)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (1 <= (Zlength (fs)))) (PreH13 : ((Zlength (fs)) <= 30)) (PreH14 : ((Zlength (all)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH16 : (AddFactorsExtract v0 v d fs )) (PreH17 : ((v % ( d ) ) = 0)),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ ((v <> (INT64_MIN)) \/ (d <> (-1))) ”
  &&  “ (d <> 0) ”
.

Definition add_factors_safety_wit_12 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) = 0)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : ((d * d ) <= v0)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (1 <= (Zlength (fs)))) (PreH13 : ((Zlength (fs)) <= 30)) (PreH14 : ((Zlength (all)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH16 : (AddFactorsExtract v0 v d fs )) (PreH17 : (AddFactorsScan v0 v d fs )),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ ((v <> (INT64_MIN)) \/ (d <> (-1))) ”
  &&  “ (d <> 0) ”
.

Definition add_factors_safety_wit_13 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) <> 0)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : ((d * d ) <= v0)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (1 <= (Zlength (fs)))) (PreH13 : ((Zlength (fs)) <= 30)) (PreH14 : ((Zlength (all)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH16 : (AddFactorsExtract v0 v d fs )) (PreH17 : (AddFactorsScan v0 v d fs )),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ ((d + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (d + 1 )) ”
.

Definition add_factors_safety_wit_14 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= v)) (PreH3 : (1 <= v0)) (PreH4 : (v0 <= 1000000001)) (PreH5 : (1 <= v)) (PreH6 : (v <= v0)) (PreH7 : (2 <= d)) (PreH8 : (d <= 31624)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (0 <= (Zlength (fs)))) (PreH13 : ((Zlength (fs)) <= 29)) (PreH14 : ((Zlength (all)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH16 : (AddFactorsScan v0 v d fs )),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ ((d + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (d + 1 )) ”
.

Definition add_factors_safety_wit_15 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (1 <= v0)) (PreH2 : (v0 <= 1000000001)) (PreH3 : (1 <= v)) (PreH4 : (v <= v0)) (PreH5 : (0 <= k0)) (PreH6 : (k0 <= 200)) (PreH7 : ((Zlength (pre)) = k0)) (PreH8 : (0 <= (Zlength (fs)))) (PreH9 : ((Zlength (fs)) <= 29)) (PreH10 : ((Zlength (all)) = 256)) (PreH11 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH12 : (AddFactorsResidual v0 v fs )),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_factors_safety_wit_16 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v > 1)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)) (PreH9 : (0 <= (Zlength (fs)))) (PreH10 : ((Zlength (fs)) <= 29)) (PreH11 : ((Zlength (all)) = 256)) (PreH12 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH13 : (AddFactorsResidual v0 v fs )),
  (Int64Array.full primes_pre 256 (replace_Znth ((k0 + (Zlength (fs)) )) (v) (all)) )
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
|--
  “ (((k0 + (Zlength (fs)) ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((k0 + (Zlength (fs)) ) + 1 )) ”
.

Definition add_factors_entail_wit_1 :=
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (v_pre: Z) (primes_pre: Z) (nprime_pre: Z) (all_2: (@list Z)) (PreH1 : ((Zlength (all_2)) = 256)) (PreH2 : ((sublist (0) (k0) (all_2)) = pre)) (PreH3 : (v_pre = v0)) (PreH4 : (1 <= v0)) (PreH5 : (v0 <= 1000000001)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)),
  (Int64Array.full primes_pre 256 all_2 )
  **  ((nprime_pre) # Int  |-> k0)
|--
  EX (all: (@list Z)) (fs: (@list Z)),
  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= v_pre) ”
  &&  “ (v_pre <= v0) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= 31624) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsScan v0 v_pre 2 fs ) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
) \/
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (v_pre: Z) (all_2: (@list Z)) (PreH1 : ((Zlength (all_2)) = 256)) (PreH2 : ((sublist (0) (k0) (all_2)) = pre)) (PreH3 : (v_pre = v0)) (PreH4 : (1 <= v0)) (PreH5 : (v0 <= 1000000001)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)),
  TT && emp 
|--
  EX (fs: (@list Z)),
  “ ((Zlength (pre)) = ((Zlength (pre)) + (Zlength (fs)) )) ”
  &&  “ (v0 <= v0) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= 31624) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((sublist (0) (((Zlength (pre)) + (Zlength (fs)) )) (all_2)) = (app ((sublist (0) ((Zlength (pre))) (all_2))) (fs))) ”
  &&  “ (AddFactorsScan v0 v0 2 fs ) ”
  &&  emp
).

Definition add_factors_entail_wit_2 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all_2: (@list Z)) (fs_2: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) = 0)) (PreH2 : ((d * d ) <= v)) (PreH3 : (1 <= v0)) (PreH4 : (v0 <= 1000000001)) (PreH5 : (1 <= v)) (PreH6 : (v <= v0)) (PreH7 : (2 <= d)) (PreH8 : (d <= 31624)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (0 <= (Zlength (fs_2)))) (PreH13 : ((Zlength (fs_2)) <= 29)) (PreH14 : ((Zlength (all_2)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all_2)) = (app (pre) (fs_2)))) (PreH16 : (AddFactorsScan v0 v d fs_2 )),
  (Int64Array.full primes_pre 256 (replace_Znth ((k0 + (Zlength (fs_2)) )) (d) (all_2)) )
  **  ((nprime_pre) # Int  |-> ((k0 + (Zlength (fs_2)) ) + 1 ))
|--
  (EX (all: (@list Z)) (fs: (@list Z)),
  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= v0) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= 31624) ”
  &&  “ ((d * d ) <= v0) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (1 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsExtract v0 v d fs ) ”
  &&  “ ((v % ( d ) ) = 0) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all ))
  ||
  (EX (all: (@list Z)) (fs: (@list Z)),
  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= v0) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= 31624) ”
  &&  “ ((d * d ) <= v0) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (1 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsExtract v0 v d fs ) ”
  &&  “ (AddFactorsScan v0 v d fs ) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all ))
.

Definition add_factors_entail_wit_3_1 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all_2: (@list Z)) (fs_2: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) = 0)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : ((d * d ) <= v0)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (1 <= (Zlength (fs_2)))) (PreH13 : ((Zlength (fs_2)) <= 30)) (PreH14 : ((Zlength (all_2)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all_2)) = (app (pre) (fs_2)))) (PreH16 : (AddFactorsExtract v0 v d fs_2 )) (PreH17 : ((v % ( d ) ) = 0)),
  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs_2)) ))
  **  (Int64Array.full primes_pre 256 all_2 )
|--
  (EX (all: (@list Z)) (fs: (@list Z)),
  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= (v ÷ d )) ”
  &&  “ ((v ÷ d ) <= v0) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= 31624) ”
  &&  “ ((d * d ) <= v0) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (1 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsExtract v0 (v ÷ d ) d fs ) ”
  &&  “ (((v ÷ d ) % ( d ) ) = 0) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all ))
  ||
  (EX (all: (@list Z)) (fs: (@list Z)),
  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= (v ÷ d )) ”
  &&  “ ((v ÷ d ) <= v0) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= 31624) ”
  &&  “ ((d * d ) <= v0) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (1 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsExtract v0 (v ÷ d ) d fs ) ”
  &&  “ (AddFactorsScan v0 (v ÷ d ) d fs ) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all ))
.

Definition add_factors_entail_wit_3_2 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all_2: (@list Z)) (fs_2: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) = 0)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : ((d * d ) <= v0)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (1 <= (Zlength (fs_2)))) (PreH13 : ((Zlength (fs_2)) <= 30)) (PreH14 : ((Zlength (all_2)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all_2)) = (app (pre) (fs_2)))) (PreH16 : (AddFactorsExtract v0 v d fs_2 )) (PreH17 : (AddFactorsScan v0 v d fs_2 )),
  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs_2)) ))
  **  (Int64Array.full primes_pre 256 all_2 )
|--
  (EX (all: (@list Z)) (fs: (@list Z)),
  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= (v ÷ d )) ”
  &&  “ ((v ÷ d ) <= v0) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= 31624) ”
  &&  “ ((d * d ) <= v0) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (1 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsExtract v0 (v ÷ d ) d fs ) ”
  &&  “ (((v ÷ d ) % ( d ) ) = 0) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all ))
  ||
  (EX (all: (@list Z)) (fs: (@list Z)),
  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= (v ÷ d )) ”
  &&  “ ((v ÷ d ) <= v0) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= 31624) ”
  &&  “ ((d * d ) <= v0) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (1 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsExtract v0 (v ÷ d ) d fs ) ”
  &&  “ (AddFactorsScan v0 (v ÷ d ) d fs ) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all ))
.

Definition add_factors_entail_wit_4 :=
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all_2: (@list Z)) (fs_2: (@list Z)) (d: Z) (v: Z) (PreH1 : ((d * d ) > v)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : (0 <= k0)) (PreH9 : (k0 <= 200)) (PreH10 : ((Zlength (pre)) = k0)) (PreH11 : (0 <= (Zlength (fs_2)))) (PreH12 : ((Zlength (fs_2)) <= 29)) (PreH13 : ((Zlength (all_2)) = 256)) (PreH14 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all_2)) = (app (pre) (fs_2)))) (PreH15 : (AddFactorsScan v0 v d fs_2 )),
  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs_2)) ))
  **  (Int64Array.full primes_pre 256 all_2 )
|--
  EX (all: (@list Z)) (fs: (@list Z)),
  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= v0) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsResidual v0 v fs ) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
) \/
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (all_2: (@list Z)) (fs_2: (@list Z)) (d: Z) (v: Z) (PreH1 : ((d * d ) > v)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : (0 <= k0)) (PreH9 : (k0 <= 200)) (PreH10 : ((Zlength (pre)) = k0)) (PreH11 : (0 <= (Zlength (fs_2)))) (PreH12 : ((Zlength (fs_2)) <= 29)) (PreH13 : ((Zlength (all_2)) = 256)) (PreH14 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all_2)) = (app (pre) (fs_2)))) (PreH15 : (AddFactorsScan v0 v d fs_2 )),
  TT && emp 
|--
  EX (fs: (@list Z)),
  “ (((Zlength (pre)) + (Zlength (fs_2)) ) = ((Zlength (pre)) + (Zlength (fs)) )) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((sublist (0) (((Zlength (pre)) + (Zlength (fs)) )) (all_2)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsResidual v0 v fs ) ”
  &&  emp
).

Definition add_factors_entail_wit_5_1 :=
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all_2: (@list Z)) (fs_2: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) <> 0)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : ((d * d ) <= v0)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (1 <= (Zlength (fs_2)))) (PreH13 : ((Zlength (fs_2)) <= 30)) (PreH14 : ((Zlength (all_2)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all_2)) = (app (pre) (fs_2)))) (PreH16 : (AddFactorsExtract v0 v d fs_2 )) (PreH17 : (AddFactorsScan v0 v d fs_2 )),
  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs_2)) ))
  **  (Int64Array.full primes_pre 256 all_2 )
|--
  EX (all: (@list Z)) (fs: (@list Z)),
  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= v0) ”
  &&  “ (2 <= (d + 1 )) ”
  &&  “ ((d + 1 ) <= 31624) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsScan v0 v (d + 1 ) fs ) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
) \/
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (all_2: (@list Z)) (fs_2: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) <> 0)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (2 <= d)) (PreH7 : (d <= 31624)) (PreH8 : ((d * d ) <= v0)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (1 <= (Zlength (fs_2)))) (PreH13 : ((Zlength (fs_2)) <= 30)) (PreH14 : ((Zlength (all_2)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all_2)) = (app (pre) (fs_2)))) (PreH16 : (AddFactorsExtract v0 v d fs_2 )) (PreH17 : (AddFactorsScan v0 v d fs_2 )),
  TT && emp 
|--
  EX (fs: (@list Z)),
  “ (((Zlength (pre)) + (Zlength (fs_2)) ) = ((Zlength (pre)) + (Zlength (fs)) )) ”
  &&  “ (2 <= (d + 1 )) ”
  &&  “ ((d + 1 ) <= 31624) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((sublist (0) (((Zlength (pre)) + (Zlength (fs)) )) (all_2)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsScan v0 v (d + 1 ) fs ) ”
  &&  emp
).

Definition add_factors_entail_wit_5_2 :=
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all_2: (@list Z)) (fs_2: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= v)) (PreH3 : (1 <= v0)) (PreH4 : (v0 <= 1000000001)) (PreH5 : (1 <= v)) (PreH6 : (v <= v0)) (PreH7 : (2 <= d)) (PreH8 : (d <= 31624)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (0 <= (Zlength (fs_2)))) (PreH13 : ((Zlength (fs_2)) <= 29)) (PreH14 : ((Zlength (all_2)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all_2)) = (app (pre) (fs_2)))) (PreH16 : (AddFactorsScan v0 v d fs_2 )),
  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs_2)) ))
  **  (Int64Array.full primes_pre 256 all_2 )
|--
  EX (all: (@list Z)) (fs: (@list Z)),
  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= v0) ”
  &&  “ (2 <= (d + 1 )) ”
  &&  “ ((d + 1 ) <= 31624) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsScan v0 v (d + 1 ) fs ) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
) \/
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (all_2: (@list Z)) (fs_2: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= v)) (PreH3 : (1 <= v0)) (PreH4 : (v0 <= 1000000001)) (PreH5 : (1 <= v)) (PreH6 : (v <= v0)) (PreH7 : (2 <= d)) (PreH8 : (d <= 31624)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (0 <= (Zlength (fs_2)))) (PreH13 : ((Zlength (fs_2)) <= 29)) (PreH14 : ((Zlength (all_2)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all_2)) = (app (pre) (fs_2)))) (PreH16 : (AddFactorsScan v0 v d fs_2 )),
  TT && emp 
|--
  EX (fs: (@list Z)),
  “ (((Zlength (pre)) + (Zlength (fs_2)) ) = ((Zlength (pre)) + (Zlength (fs)) )) ”
  &&  “ (2 <= (d + 1 )) ”
  &&  “ ((d + 1 ) <= 31624) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((sublist (0) (((Zlength (pre)) + (Zlength (fs)) )) (all_2)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsScan v0 v (d + 1 ) fs ) ”
  &&  emp
).

Definition add_factors_return_wit_1 :=
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs_2: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v > 1)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)) (PreH9 : (0 <= (Zlength (fs_2)))) (PreH10 : ((Zlength (fs_2)) <= 29)) (PreH11 : ((Zlength (all)) = 256)) (PreH12 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all)) = (app (pre) (fs_2)))) (PreH13 : (AddFactorsResidual v0 v fs_2 )),
  ((nprime_pre) # Int  |-> ((k0 + (Zlength (fs_2)) ) + 1 ))
  **  (Int64Array.seg primes_pre 0 ((k0 + (Zlength (fs_2)) ) + 1 ) (sublist (0) (((k0 + (Zlength (fs_2)) ) + 1 )) ((replace_Znth ((k0 + (Zlength (fs_2)) )) (v) (all)))) )
  **  (Int64Array.seg_shape primes_pre ((k0 + (Zlength (fs_2)) ) + 1 ) 256 )
|--
  EX (fs: (@list Z)),
  “ (AddFactorsResult v0 fs ) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.seg primes_pre 0 (k0 + (Zlength (fs)) ) (app (pre) (fs)) )
  **  (Int64Array.seg_shape primes_pre (k0 + (Zlength (fs)) ) 256 )
) \/
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (fs_2: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v > 1)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)) (PreH9 : (0 <= (Zlength (fs_2)))) (PreH10 : ((Zlength (fs_2)) <= 29)) (PreH11 : ((Zlength (all)) = 256)) (PreH12 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all)) = (app (pre) (fs_2)))) (PreH13 : (AddFactorsResidual v0 v fs_2 )),
  (Int64Array.seg primes_pre 0 ((k0 + (Zlength (fs_2)) ) + 1 ) (sublist (0) (((k0 + (Zlength (fs_2)) ) + 1 )) ((replace_Znth ((k0 + (Zlength (fs_2)) )) (v) (all)))) )
  **  (Int64Array.seg_shape primes_pre ((k0 + (Zlength (fs_2)) ) + 1 ) 256 )
|--
  EX (fs: (@list Z)),
  “ (((k0 + (Zlength (fs_2)) ) + 1 ) = (k0 + (Zlength (fs)) )) ”
  &&  “ (AddFactorsResult v0 fs ) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  (Int64Array.seg primes_pre 0 (k0 + (Zlength (fs)) ) (app (pre) (fs)) )
  **  (Int64Array.seg_shape primes_pre (k0 + (Zlength (fs)) ) 256 )
).

Definition add_factors_return_wit_2 :=
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs_2: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v <= 1)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)) (PreH9 : (0 <= (Zlength (fs_2)))) (PreH10 : ((Zlength (fs_2)) <= 29)) (PreH11 : ((Zlength (all)) = 256)) (PreH12 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all)) = (app (pre) (fs_2)))) (PreH13 : (AddFactorsResidual v0 v fs_2 )),
  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs_2)) ))
  **  (Int64Array.seg primes_pre 0 (k0 + (Zlength (fs_2)) ) (sublist (0) ((k0 + (Zlength (fs_2)) )) (all)) )
  **  (Int64Array.seg_shape primes_pre (k0 + (Zlength (fs_2)) ) 256 )
|--
  EX (fs: (@list Z)),
  “ (AddFactorsResult v0 fs ) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.seg primes_pre 0 (k0 + (Zlength (fs)) ) (app (pre) (fs)) )
  **  (Int64Array.seg_shape primes_pre (k0 + (Zlength (fs)) ) 256 )
) \/
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (fs_2: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v <= 1)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)) (PreH9 : (0 <= (Zlength (fs_2)))) (PreH10 : ((Zlength (fs_2)) <= 29)) (PreH11 : ((Zlength (all)) = 256)) (PreH12 : ((sublist (0) ((k0 + (Zlength (fs_2)) )) (all)) = (app (pre) (fs_2)))) (PreH13 : (AddFactorsResidual v0 v fs_2 )),
  (Int64Array.seg primes_pre 0 (k0 + (Zlength (fs_2)) ) (sublist (0) ((k0 + (Zlength (fs_2)) )) (all)) )
  **  (Int64Array.seg_shape primes_pre (k0 + (Zlength (fs_2)) ) 256 )
|--
  EX (fs: (@list Z)),
  “ ((k0 + (Zlength (fs_2)) ) = (k0 + (Zlength (fs)) )) ”
  &&  “ (AddFactorsResult v0 fs ) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  (Int64Array.seg primes_pre 0 (k0 + (Zlength (fs)) ) (app (pre) (fs)) )
  **  (Int64Array.seg_shape primes_pre (k0 + (Zlength (fs)) ) 256 )
).

Definition add_factors_partial_solve_wit_1_pure :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (v_pre: Z) (primes_pre: Z) (nprime_pre: Z) (PreH1 : (v_pre = v0)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (0 <= k0)) (PreH5 : (k0 <= 200)) (PreH6 : ((Zlength (pre)) = k0)),
  ((( &( "v" ) )) # Int64  |-> v_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((nprime_pre) # Int  |-> k0)
  **  (Int64Array.seg primes_pre 0 k0 pre )
  **  (Int64Array.seg_shape primes_pre k0 256 )
|--
  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
.

Definition add_factors_partial_solve_wit_1_aux :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (v_pre: Z) (primes_pre: Z) (nprime_pre: Z) (PreH1 : (v_pre = v0)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (0 <= k0)) (PreH5 : (k0 <= 200)) (PreH6 : ((Zlength (pre)) = k0)),
  ((nprime_pre) # Int  |-> k0)
  **  (Int64Array.seg primes_pre 0 k0 pre )
  **  (Int64Array.seg_shape primes_pre k0 256 )
|--
  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (v_pre = v0) ”
  &&  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  (Int64Array.seg primes_pre 0 k0 pre )
  **  (Int64Array.seg_shape primes_pre k0 256 )
  **  ((nprime_pre) # Int  |-> k0)
.

Definition add_factors_partial_solve_wit_1 := add_factors_partial_solve_wit_1_pure -> add_factors_partial_solve_wit_1_aux.

Definition add_factors_partial_solve_wit_2 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (all: (@list Z)) (fs: (@list Z)) (d: Z) (v: Z) (PreH1 : ((v % ( d ) ) = 0)) (PreH2 : ((d * d ) <= v)) (PreH3 : (1 <= v0)) (PreH4 : (v0 <= 1000000001)) (PreH5 : (1 <= v)) (PreH6 : (v <= v0)) (PreH7 : (2 <= d)) (PreH8 : (d <= 31624)) (PreH9 : (0 <= k0)) (PreH10 : (k0 <= 200)) (PreH11 : ((Zlength (pre)) = k0)) (PreH12 : (0 <= (Zlength (fs)))) (PreH13 : ((Zlength (fs)) <= 29)) (PreH14 : ((Zlength (all)) = 256)) (PreH15 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH16 : (AddFactorsScan v0 v d fs )),
  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ ((v % ( d ) ) = 0) ”
  &&  “ ((d * d ) <= v) ”
  &&  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= v0) ”
  &&  “ (2 <= d) ”
  &&  “ (d <= 31624) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsScan v0 v d fs ) ”
  &&  (((primes_pre + ((k0 + (Zlength (fs)) ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i primes_pre (k0 + (Zlength (fs)) ) 0 256 all )
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
.

Definition add_factors_partial_solve_wit_3 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v > 1)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)) (PreH9 : (0 <= (Zlength (fs)))) (PreH10 : ((Zlength (fs)) <= 29)) (PreH11 : ((Zlength (all)) = 256)) (PreH12 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH13 : (AddFactorsResidual v0 v fs )),
  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ (v > 1) ”
  &&  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= v0) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsResidual v0 v fs ) ”
  &&  (((primes_pre + ((k0 + (Zlength (fs)) ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i primes_pre (k0 + (Zlength (fs)) ) 0 256 all )
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
.

Definition add_factors_partial_solve_wit_4_pure :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v <= 1)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)) (PreH9 : (0 <= (Zlength (fs)))) (PreH10 : ((Zlength (fs)) <= 29)) (PreH11 : ((Zlength (all)) = 256)) (PreH12 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH13 : (AddFactorsResidual v0 v fs )),
  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ (0 <= (k0 + (Zlength (fs)) )) ”
  &&  “ ((k0 + (Zlength (fs)) ) <= 256) ”
  &&  “ ((Zlength (all)) = 256) ”
.

Definition add_factors_partial_solve_wit_4_aux :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v <= 1)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)) (PreH9 : (0 <= (Zlength (fs)))) (PreH10 : ((Zlength (fs)) <= 29)) (PreH11 : ((Zlength (all)) = 256)) (PreH12 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH13 : (AddFactorsResidual v0 v fs )),
  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
|--
  “ (0 <= (k0 + (Zlength (fs)) )) ”
  &&  “ ((k0 + (Zlength (fs)) ) <= 256) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ (v <= 1) ”
  &&  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= v0) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsResidual v0 v fs ) ”
  &&  ((nprime_pre) # Int  |-> (k0 + (Zlength (fs)) ))
  **  (Int64Array.full primes_pre 256 all )
.

Definition add_factors_partial_solve_wit_4 := add_factors_partial_solve_wit_4_pure -> add_factors_partial_solve_wit_4_aux.

Definition add_factors_partial_solve_wit_5_pure :=
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v > 1)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)) (PreH9 : (0 <= (Zlength (fs)))) (PreH10 : ((Zlength (fs)) <= 29)) (PreH11 : ((Zlength (all)) = 256)) (PreH12 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH13 : (AddFactorsResidual v0 v fs )),
  (Int64Array.full primes_pre 256 (replace_Znth ((k0 + (Zlength (fs)) )) (v) (all)) )
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((nprime_pre) # Int  |-> ((k0 + (Zlength (fs)) ) + 1 ))
|--
  “ (0 <= ((k0 + (Zlength (fs)) ) + 1 )) ”
  &&  “ (((k0 + (Zlength (fs)) ) + 1 ) <= 256) ”
  &&  “ ((Zlength ((replace_Znth ((k0 + (Zlength (fs)) )) (v) (all)))) = 256) ”
) \/
(
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v <= INT64_MAX)) (PreH2 : (v >= INT64_MIN)) (PreH3 : (((k0 + (Zlength (fs)) ) + 1 ) <= INT_MAX)) (PreH4 : (((k0 + (Zlength (fs)) ) + 1 ) >= INT_MIN)) (PreH5 : (v > 1)) (PreH6 : (1 <= v0)) (PreH7 : (v0 <= 1000000001)) (PreH8 : (1 <= v)) (PreH9 : (v <= v0)) (PreH10 : (0 <= k0)) (PreH11 : (k0 <= 200)) (PreH12 : ((Zlength (pre)) = k0)) (PreH13 : (0 <= (Zlength (fs)))) (PreH14 : ((Zlength (fs)) <= 29)) (PreH15 : ((Zlength (all)) = 256)) (PreH16 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH17 : (AddFactorsResidual v0 v fs )),
  (Int64Array.full primes_pre 256 (replace_Znth ((k0 + (Zlength (fs)) )) (v) (all)) )
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((nprime_pre) # Int  |-> ((k0 + (Zlength (fs)) ) + 1 ))
|--
  “ ((Zlength ((replace_Znth ((k0 + (Zlength (fs)) )) (v) (all)))) = 256) ”
).

Definition add_factors_partial_solve_wit_5_pure_split_goal_1 :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v <= INT64_MAX)) (PreH2 : (v >= INT64_MIN)) (PreH3 : (((k0 + (Zlength (fs)) ) + 1 ) <= INT_MAX)) (PreH4 : (((k0 + (Zlength (fs)) ) + 1 ) >= INT_MIN)) (PreH5 : (v > 1)) (PreH6 : (1 <= v0)) (PreH7 : (v0 <= 1000000001)) (PreH8 : (1 <= v)) (PreH9 : (v <= v0)) (PreH10 : (0 <= k0)) (PreH11 : (k0 <= 200)) (PreH12 : ((Zlength (pre)) = k0)) (PreH13 : (0 <= (Zlength (fs)))) (PreH14 : ((Zlength (fs)) <= 29)) (PreH15 : ((Zlength (all)) = 256)) (PreH16 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH17 : (AddFactorsResidual v0 v fs )),
  (Int64Array.full primes_pre 256 (replace_Znth ((k0 + (Zlength (fs)) )) (v) (all)) )
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Ptr  |-> nprime_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((nprime_pre) # Int  |-> ((k0 + (Zlength (fs)) ) + 1 ))
|--
  “ ((Zlength ((replace_Znth ((k0 + (Zlength (fs)) )) (v) (all)))) = 256) ”
.

Definition add_factors_partial_solve_wit_5_aux :=
forall (pre: (@list Z)) (k0: Z) (v0: Z) (primes_pre: Z) (nprime_pre: Z) (fs: (@list Z)) (all: (@list Z)) (v: Z) (PreH1 : (v > 1)) (PreH2 : (1 <= v0)) (PreH3 : (v0 <= 1000000001)) (PreH4 : (1 <= v)) (PreH5 : (v <= v0)) (PreH6 : (0 <= k0)) (PreH7 : (k0 <= 200)) (PreH8 : ((Zlength (pre)) = k0)) (PreH9 : (0 <= (Zlength (fs)))) (PreH10 : ((Zlength (fs)) <= 29)) (PreH11 : ((Zlength (all)) = 256)) (PreH12 : ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs)))) (PreH13 : (AddFactorsResidual v0 v fs )),
  (Int64Array.full primes_pre 256 (replace_Znth ((k0 + (Zlength (fs)) )) (v) (all)) )
  **  ((nprime_pre) # Int  |-> ((k0 + (Zlength (fs)) ) + 1 ))
|--
  “ (0 <= ((k0 + (Zlength (fs)) ) + 1 )) ”
  &&  “ (((k0 + (Zlength (fs)) ) + 1 ) <= 256) ”
  &&  “ ((Zlength ((replace_Znth ((k0 + (Zlength (fs)) )) (v) (all)))) = 256) ”
  &&  “ (v > 1) ”
  &&  “ (1 <= v0) ”
  &&  “ (v0 <= 1000000001) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= v0) ”
  &&  “ (0 <= k0) ”
  &&  “ (k0 <= 200) ”
  &&  “ ((Zlength (pre)) = k0) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 29) ”
  &&  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) ((k0 + (Zlength (fs)) )) (all)) = (app (pre) (fs))) ”
  &&  “ (AddFactorsResidual v0 v fs ) ”
  &&  ((nprime_pre) # Int  |-> ((k0 + (Zlength (fs)) ) + 1 ))
  **  (Int64Array.full primes_pre 256 (replace_Znth ((k0 + (Zlength (fs)) )) (v) (all)) )
.

Definition add_factors_partial_solve_wit_5 := add_factors_partial_solve_wit_5_pure -> add_factors_partial_solve_wit_5_aux.

Definition add_factors_which_implies_wit_1 :=
(
forall (pre: (@list Z)) (k0: Z) (primes: Z) (PreH1 : (0 <= k0)) (PreH2 : (k0 <= 200)) (PreH3 : ((Zlength (pre)) = k0)),
  (Int64Array.seg primes 0 k0 pre )
  **  (Int64Array.seg_shape primes k0 256 )
|--
  EX (all: (@list Z)),
  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) (k0) (all)) = pre) ”
  &&  (Int64Array.full primes 256 all )
) \/
(
forall (pre: (@list Z)) (k0: Z) (primes: Z) (PreH1 : (0 <= k0)) (PreH2 : (k0 <= 200)) (PreH3 : ((Zlength (pre)) = k0)),
  (Int64Array.seg primes 0 k0 pre )
  **  (Int64Array.seg_shape primes k0 256 )
|--
  EX (all: (@list Z)),
  “ ((Zlength (all)) = 256) ”
  &&  “ ((sublist (0) (k0) (all)) = pre) ”
  &&  (Int64Array.full primes 256 all )
).

Definition add_factors_which_implies_wit_2 :=
(
forall (m: Z) (all: (@list Z)) (nprime: Z) (primes: Z) (PreH1 : (0 <= m)) (PreH2 : (m <= 256)) (PreH3 : ((Zlength (all)) = 256)),
  ((nprime) # Int  |-> m)
  **  (Int64Array.full primes 256 all )
|--
  ((nprime) # Int  |-> m)
  **  (Int64Array.seg primes 0 m (sublist (0) (m) (all)) )
  **  (Int64Array.seg_shape primes m 256 )
) \/
(
forall (m: Z) (all: (@list Z)) (primes: Z) (PreH1 : (0 <= m)) (PreH2 : (m <= 256)) (PreH3 : ((Zlength (all)) = 256)),
  (Int64Array.full primes 256 all )
|--
  (Int64Array.seg primes 0 m (sublist (0) (m) (all)) )
  **  (Int64Array.seg_shape primes m 256 )
).

Definition add_factors_which_implies_wit_2_split_goal_spatial :=
forall (m: Z) (all: (@list Z)) (primes: Z) (PreH1 : (0 <= m)) (PreH2 : (m <= 256)) (PreH3 : ((Zlength (all)) = 256)),
  (Int64Array.full primes 256 all )
|--
  (Int64Array.seg primes 0 m (sublist (0) (m) (all)) )
  **  (Int64Array.seg_shape primes m 256 )
.

(*----- Function cost_for_prime -----*)

Definition cost_for_prime_safety_wit_1 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  ((( &( "after" ) )) # Int64  |->_)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "cutFresh" ) )) # Int64  |-> 0)
  **  ((( &( "keep" ) )) # Int64  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_2 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  ((( &( "after" ) )) # Int64  |->_)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "cutFresh" ) )) # Int64  |-> 0)
  **  ((( &( "keep" ) )) # Int64  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_3 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  ((( &( "after" ) )) # Int64  |->_)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "cutFresh" ) )) # Int64  |-> 0)
  **  ((( &( "keep" ) )) # Int64  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_4 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  ((( &( "cutAfterKeep" ) )) # Int64  |->_)
  **  ((( &( "cutFresh" ) )) # Int64  |-> 0)
  **  ((( &( "keep" ) )) # Int64  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_5 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  ((( &( "cutAfterKeep" ) )) # Int64  |->_)
  **  ((( &( "cutFresh" ) )) # Int64  |-> 0)
  **  ((( &( "keep" ) )) # Int64  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_6 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  ((( &( "cutAfterKeep" ) )) # Int64  |->_)
  **  ((( &( "cutFresh" ) )) # Int64  |-> 0)
  **  ((( &( "keep" ) )) # Int64  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_7 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  ((( &( "cutFresh" ) )) # Int64  |->_)
  **  ((( &( "keep" ) )) # Int64  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cost_for_prime_safety_wit_8 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  ((( &( "keep" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cost_for_prime_safety_wit_9 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "after" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "cutFresh" ) )) # Int64  |-> 0)
  **  ((( &( "keep" ) )) # Int64  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cost_for_prime_safety_wit_10 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (2 <= p_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= keep)) (PreH14 : (keep <= 4611686018427387904)) (PreH15 : (0 <= cutFresh)) (PreH16 : (cutFresh <= 4611686018427387904)) (PreH17 : (0 <= cutAfterKeep)) (PreH18 : (cutAfterKeep <= 4611686018427387904)) (PreH19 : (0 <= after)) (PreH20 : (after <= 4611686018427387904)) (PreH21 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (((Znth i values 0) <> (INT64_MIN)) \/ (p_pre <> (-1))) ”
  &&  “ (p_pre <> 0) ”
.

Definition cost_for_prime_safety_wit_11 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (2 <= p_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= keep)) (PreH14 : (keep <= 4611686018427387904)) (PreH15 : (0 <= cutFresh)) (PreH16 : (cutFresh <= 4611686018427387904)) (PreH17 : (0 <= cutAfterKeep)) (PreH18 : (cutAfterKeep <= 4611686018427387904)) (PreH19 : (0 <= after)) (PreH20 : (after <= 4611686018427387904)) (PreH21 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cost_for_prime_safety_wit_12 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (((Znth i values 0) % ( p_pre ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= keep)) (PreH15 : (keep <= 4611686018427387904)) (PreH16 : (0 <= cutFresh)) (PreH17 : (cutFresh <= 4611686018427387904)) (PreH18 : (0 <= cutAfterKeep)) (PreH19 : (cutAfterKeep <= 4611686018427387904)) (PreH20 : (0 <= after)) (PreH21 : (after <= 4611686018427387904)) (PreH22 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cost_for_prime_safety_wit_13 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= keep)) (PreH15 : (keep <= 4611686018427387904)) (PreH16 : (0 <= cutFresh)) (PreH17 : (cutFresh <= 4611686018427387904)) (PreH18 : (0 <= cutAfterKeep)) (PreH19 : (cutAfterKeep <= 4611686018427387904)) (PreH20 : (0 <= after)) (PreH21 : (after <= 4611686018427387904)) (PreH22 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ ((((Znth i values 0) - 1 ) <> (INT64_MIN)) \/ (p_pre <> (-1))) ”
  &&  “ (p_pre <> 0) ”
.

Definition cost_for_prime_safety_wit_14 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= keep)) (PreH15 : (keep <= 4611686018427387904)) (PreH16 : (0 <= cutFresh)) (PreH17 : (cutFresh <= 4611686018427387904)) (PreH18 : (0 <= cutAfterKeep)) (PreH19 : (cutAfterKeep <= 4611686018427387904)) (PreH20 : (0 <= after)) (PreH21 : (after <= 4611686018427387904)) (PreH22 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (((Znth i values 0) - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i values 0) - 1 )) ”
.

Definition cost_for_prime_safety_wit_15 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= keep)) (PreH15 : (keep <= 4611686018427387904)) (PreH16 : (0 <= cutFresh)) (PreH17 : (cutFresh <= 4611686018427387904)) (PreH18 : (0 <= cutAfterKeep)) (PreH19 : (cutAfterKeep <= 4611686018427387904)) (PreH20 : (0 <= after)) (PreH21 : (after <= 4611686018427387904)) (PreH22 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_16 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= keep)) (PreH15 : (keep <= 4611686018427387904)) (PreH16 : (0 <= cutFresh)) (PreH17 : (cutFresh <= 4611686018427387904)) (PreH18 : (0 <= cutAfterKeep)) (PreH19 : (cutAfterKeep <= 4611686018427387904)) (PreH20 : (0 <= after)) (PreH21 : (after <= 4611686018427387904)) (PreH22 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cost_for_prime_safety_wit_17 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH2 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= keep)) (PreH16 : (keep <= 4611686018427387904)) (PreH17 : (0 <= cutFresh)) (PreH18 : (cutFresh <= 4611686018427387904)) (PreH19 : (0 <= cutAfterKeep)) (PreH20 : (cutAfterKeep <= 4611686018427387904)) (PreH21 : (0 <= after)) (PreH22 : (after <= 4611686018427387904)) (PreH23 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ ((((Znth i values 0) + 1 ) <> (INT64_MIN)) \/ (p_pre <> (-1))) ”
  &&  “ (p_pre <> 0) ”
.

Definition cost_for_prime_safety_wit_18 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH2 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= keep)) (PreH16 : (keep <= 4611686018427387904)) (PreH17 : (0 <= cutFresh)) (PreH18 : (cutFresh <= 4611686018427387904)) (PreH19 : (0 <= cutAfterKeep)) (PreH20 : (cutAfterKeep <= 4611686018427387904)) (PreH21 : (0 <= after)) (PreH22 : (after <= 4611686018427387904)) (PreH23 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (((Znth i values 0) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i values 0) + 1 )) ”
.

Definition cost_for_prime_safety_wit_19 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH2 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= keep)) (PreH16 : (keep <= 4611686018427387904)) (PreH17 : (0 <= cutFresh)) (PreH18 : (cutFresh <= 4611686018427387904)) (PreH19 : (0 <= cutAfterKeep)) (PreH20 : (cutAfterKeep <= 4611686018427387904)) (PreH21 : (0 <= after)) (PreH22 : (after <= 4611686018427387904)) (PreH23 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_20 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH2 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= keep)) (PreH16 : (keep <= 4611686018427387904)) (PreH17 : (0 <= cutFresh)) (PreH18 : (cutFresh <= 4611686018427387904)) (PreH19 : (0 <= cutAfterKeep)) (PreH20 : (cutAfterKeep <= 4611686018427387904)) (PreH21 : (0 <= after)) (PreH22 : (after <= 4611686018427387904)) (PreH23 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cost_for_prime_safety_wit_21 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) <> 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_22 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) <> 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_23 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) <> 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "cost" ) )) # Int64  |->_)
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "v" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_24 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (2 <= v)) (PreH14 : (v <= 1000000000)) (PreH15 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 4611686018427387904)) (PreH18 : (0 <= keep)) (PreH19 : (keep <= 4611686018427387904)) (PreH20 : (0 <= cutFresh)) (PreH21 : (cutFresh <= 4611686018427387904)) (PreH22 : (0 <= cutAfterKeep)) (PreH23 : (cutAfterKeep <= 4611686018427387904)) (PreH24 : (0 <= after)) (PreH25 : (after <= 4611686018427387904)) (PreH26 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nkeep" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_25 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (2 <= v)) (PreH14 : (v <= 1000000000)) (PreH15 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 4611686018427387904)) (PreH18 : (0 <= keep)) (PreH19 : (keep <= 4611686018427387904)) (PreH20 : (0 <= cutFresh)) (PreH21 : (cutFresh <= 4611686018427387904)) (PreH22 : (0 <= cutAfterKeep)) (PreH23 : (cutAfterKeep <= 4611686018427387904)) (PreH24 : (0 <= after)) (PreH25 : (after <= 4611686018427387904)) (PreH26 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nkeep" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_26 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (2 <= v)) (PreH14 : (v <= 1000000000)) (PreH15 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 4611686018427387904)) (PreH18 : (0 <= keep)) (PreH19 : (keep <= 4611686018427387904)) (PreH20 : (0 <= cutFresh)) (PreH21 : (cutFresh <= 4611686018427387904)) (PreH22 : (0 <= cutAfterKeep)) (PreH23 : (cutAfterKeep <= 4611686018427387904)) (PreH24 : (0 <= after)) (PreH25 : (after <= 4611686018427387904)) (PreH26 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nkeep" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_27 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep <> (Z.shiftl 1 62))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (2 <= p_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (2 <= v)) (PreH15 : (v <= 1000000000)) (PreH16 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH17 : (0 <= cost)) (PreH18 : (cost <= 4611686018427387904)) (PreH19 : (0 <= keep)) (PreH20 : (keep <= 4611686018427387904)) (PreH21 : (0 <= cutFresh)) (PreH22 : (cutFresh <= 4611686018427387904)) (PreH23 : (0 <= cutAfterKeep)) (PreH24 : (cutAfterKeep <= 4611686018427387904)) (PreH25 : (0 <= after)) (PreH26 : (after <= 4611686018427387904)) (PreH27 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nkeep" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ False ”
.

Definition cost_for_prime_safety_wit_28 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep = (Z.shiftl 1 62))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (2 <= p_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (2 <= v)) (PreH15 : (v <= 1000000000)) (PreH16 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH17 : (0 <= cost)) (PreH18 : (cost <= 4611686018427387904)) (PreH19 : (0 <= keep)) (PreH20 : (keep <= 4611686018427387904)) (PreH21 : (0 <= cutFresh)) (PreH22 : (cutFresh <= 4611686018427387904)) (PreH23 : (0 <= cutAfterKeep)) (PreH24 : (cutAfterKeep <= 4611686018427387904)) (PreH25 : (0 <= after)) (PreH26 : (after <= 4611686018427387904)) (PreH27 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nkeep" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_29 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep = (Z.shiftl 1 62))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (2 <= p_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (2 <= v)) (PreH15 : (v <= 1000000000)) (PreH16 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH17 : (0 <= cost)) (PreH18 : (cost <= 4611686018427387904)) (PreH19 : (0 <= keep)) (PreH20 : (keep <= 4611686018427387904)) (PreH21 : (0 <= cutFresh)) (PreH22 : (cutFresh <= 4611686018427387904)) (PreH23 : (0 <= cutAfterKeep)) (PreH24 : (cutAfterKeep <= 4611686018427387904)) (PreH25 : (0 <= after)) (PreH26 : (after <= 4611686018427387904)) (PreH27 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nkeep" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_30 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep = (Z.shiftl 1 62))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (2 <= p_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (2 <= v)) (PreH15 : (v <= 1000000000)) (PreH16 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH17 : (0 <= cost)) (PreH18 : (cost <= 4611686018427387904)) (PreH19 : (0 <= keep)) (PreH20 : (keep <= 4611686018427387904)) (PreH21 : (0 <= cutFresh)) (PreH22 : (cutFresh <= 4611686018427387904)) (PreH23 : (0 <= cutAfterKeep)) (PreH24 : (cutAfterKeep <= 4611686018427387904)) (PreH25 : (0 <= after)) (PreH26 : (after <= 4611686018427387904)) (PreH27 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nkeep" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_31 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min ((Z.shiftl 1 62)) ((keep + cost ))) = (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))) (PreH2 : (keep = (Z.shiftl 1 62))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (v = (Znth i values 0))) (PreH15 : (2 <= v)) (PreH16 : (v <= 1000000000)) (PreH17 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH18 : (0 <= cost)) (PreH19 : (cost <= 4611686018427387904)) (PreH20 : (0 <= keep)) (PreH21 : (keep <= 4611686018427387904)) (PreH22 : (0 <= cutFresh)) (PreH23 : (cutFresh <= 4611686018427387904)) (PreH24 : (0 <= cutAfterKeep)) (PreH25 : (cutAfterKeep <= 4611686018427387904)) (PreH26 : (0 <= after)) (PreH27 : (after <= 4611686018427387904)) (PreH28 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutFresh" ) )) # Int64  |->_)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_32 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min ((Z.shiftl 1 62)) ((keep + cost ))) = (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))) (PreH2 : (keep = (Z.shiftl 1 62))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (v = (Znth i values 0))) (PreH15 : (2 <= v)) (PreH16 : (v <= 1000000000)) (PreH17 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH18 : (0 <= cost)) (PreH19 : (cost <= 4611686018427387904)) (PreH20 : (0 <= keep)) (PreH21 : (keep <= 4611686018427387904)) (PreH22 : (0 <= cutFresh)) (PreH23 : (cutFresh <= 4611686018427387904)) (PreH24 : (0 <= cutAfterKeep)) (PreH25 : (cutAfterKeep <= 4611686018427387904)) (PreH26 : (0 <= after)) (PreH27 : (after <= 4611686018427387904)) (PreH28 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutFresh" ) )) # Int64  |->_)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_33 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min ((Z.shiftl 1 62)) ((keep + cost ))) = (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))) (PreH2 : (keep = (Z.shiftl 1 62))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (v = (Znth i values 0))) (PreH15 : (2 <= v)) (PreH16 : (v <= 1000000000)) (PreH17 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH18 : (0 <= cost)) (PreH19 : (cost <= 4611686018427387904)) (PreH20 : (0 <= keep)) (PreH21 : (keep <= 4611686018427387904)) (PreH22 : (0 <= cutFresh)) (PreH23 : (cutFresh <= 4611686018427387904)) (PreH24 : (0 <= cutAfterKeep)) (PreH25 : (cutAfterKeep <= 4611686018427387904)) (PreH26 : (0 <= after)) (PreH27 : (after <= 4611686018427387904)) (PreH28 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutFresh" ) )) # Int64  |->_)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_34 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutFresh <> (Z.shiftl 1 62))) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((keep + cost ))) = (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))) (PreH3 : (keep = (Z.shiftl 1 62))) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (v = (Znth i values 0))) (PreH16 : (2 <= v)) (PreH17 : (v <= 1000000000)) (PreH18 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH19 : (0 <= cost)) (PreH20 : (cost <= 4611686018427387904)) (PreH21 : (0 <= keep)) (PreH22 : (keep <= 4611686018427387904)) (PreH23 : (0 <= cutFresh)) (PreH24 : (cutFresh <= 4611686018427387904)) (PreH25 : (0 <= cutAfterKeep)) (PreH26 : (cutAfterKeep <= 4611686018427387904)) (PreH27 : (0 <= after)) (PreH28 : (after <= 4611686018427387904)) (PreH29 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutFresh" ) )) # Int64  |->_)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ False ”
.

Definition cost_for_prime_safety_wit_35 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutFresh = (Z.shiftl 1 62))) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((keep + cost ))) = (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))) (PreH3 : (keep = (Z.shiftl 1 62))) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (v = (Znth i values 0))) (PreH16 : (2 <= v)) (PreH17 : (v <= 1000000000)) (PreH18 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH19 : (0 <= cost)) (PreH20 : (cost <= 4611686018427387904)) (PreH21 : (0 <= keep)) (PreH22 : (keep <= 4611686018427387904)) (PreH23 : (0 <= cutFresh)) (PreH24 : (cutFresh <= 4611686018427387904)) (PreH25 : (0 <= cutAfterKeep)) (PreH26 : (cutAfterKeep <= 4611686018427387904)) (PreH27 : (0 <= after)) (PreH28 : (after <= 4611686018427387904)) (PreH29 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutFresh" ) )) # Int64  |->_)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_36 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutFresh = (Z.shiftl 1 62))) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((keep + cost ))) = (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))) (PreH3 : (keep = (Z.shiftl 1 62))) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (v = (Znth i values 0))) (PreH16 : (2 <= v)) (PreH17 : (v <= 1000000000)) (PreH18 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH19 : (0 <= cost)) (PreH20 : (cost <= 4611686018427387904)) (PreH21 : (0 <= keep)) (PreH22 : (keep <= 4611686018427387904)) (PreH23 : (0 <= cutFresh)) (PreH24 : (cutFresh <= 4611686018427387904)) (PreH25 : (0 <= cutAfterKeep)) (PreH26 : (cutAfterKeep <= 4611686018427387904)) (PreH27 : (0 <= after)) (PreH28 : (after <= 4611686018427387904)) (PreH29 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutFresh" ) )) # Int64  |->_)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_37 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutFresh = (Z.shiftl 1 62))) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((keep + cost ))) = (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))) (PreH3 : (keep = (Z.shiftl 1 62))) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (v = (Znth i values 0))) (PreH16 : (2 <= v)) (PreH17 : (v <= 1000000000)) (PreH18 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH19 : (0 <= cost)) (PreH20 : (cost <= 4611686018427387904)) (PreH21 : (0 <= keep)) (PreH22 : (keep <= 4611686018427387904)) (PreH23 : (0 <= cutFresh)) (PreH24 : (cutFresh <= 4611686018427387904)) (PreH25 : (0 <= cutAfterKeep)) (PreH26 : (cutAfterKeep <= 4611686018427387904)) (PreH27 : (0 <= after)) (PreH28 : (after <= 4611686018427387904)) (PreH29 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutFresh" ) )) # Int64  |->_)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_38 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH2 : (cutFresh = (Z.shiftl 1 62))) (PreH3 : (keep = (Z.shiftl 1 62))) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (v = (Znth i values 0))) (PreH16 : (2 <= v)) (PreH17 : (v <= 1000000000)) (PreH18 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH19 : (0 <= cost)) (PreH20 : (cost <= 4611686018427387904)) (PreH21 : (0 <= keep)) (PreH22 : (keep <= 4611686018427387904)) (PreH23 : (0 <= cutFresh)) (PreH24 : (cutFresh <= 4611686018427387904)) (PreH25 : (0 <= cutAfterKeep)) (PreH26 : (cutAfterKeep <= 4611686018427387904)) (PreH27 : (0 <= after)) (PreH28 : (after <= 4611686018427387904)) (PreH29 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |->_)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_39 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH2 : (cutFresh = (Z.shiftl 1 62))) (PreH3 : (keep = (Z.shiftl 1 62))) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (v = (Znth i values 0))) (PreH16 : (2 <= v)) (PreH17 : (v <= 1000000000)) (PreH18 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH19 : (0 <= cost)) (PreH20 : (cost <= 4611686018427387904)) (PreH21 : (0 <= keep)) (PreH22 : (keep <= 4611686018427387904)) (PreH23 : (0 <= cutFresh)) (PreH24 : (cutFresh <= 4611686018427387904)) (PreH25 : (0 <= cutAfterKeep)) (PreH26 : (cutAfterKeep <= 4611686018427387904)) (PreH27 : (0 <= after)) (PreH28 : (after <= 4611686018427387904)) (PreH29 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |->_)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_40 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH2 : (cutFresh = (Z.shiftl 1 62))) (PreH3 : (keep = (Z.shiftl 1 62))) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (v = (Znth i values 0))) (PreH16 : (2 <= v)) (PreH17 : (v <= 1000000000)) (PreH18 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH19 : (0 <= cost)) (PreH20 : (cost <= 4611686018427387904)) (PreH21 : (0 <= keep)) (PreH22 : (keep <= 4611686018427387904)) (PreH23 : (0 <= cutFresh)) (PreH24 : (cutFresh <= 4611686018427387904)) (PreH25 : (0 <= cutAfterKeep)) (PreH26 : (cutAfterKeep <= 4611686018427387904)) (PreH27 : (0 <= after)) (PreH28 : (after <= 4611686018427387904)) (PreH29 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |->_)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_41 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH2 : (cutFresh = (Z.shiftl 1 62))) (PreH3 : (keep = (Z.shiftl 1 62))) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (v = (Znth i values 0))) (PreH16 : (2 <= v)) (PreH17 : (v <= 1000000000)) (PreH18 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH19 : (0 <= cost)) (PreH20 : (cost <= 4611686018427387904)) (PreH21 : (0 <= keep)) (PreH22 : (keep <= 4611686018427387904)) (PreH23 : (0 <= cutFresh)) (PreH24 : (cutFresh <= 4611686018427387904)) (PreH25 : (0 <= cutAfterKeep)) (PreH26 : (cutAfterKeep <= 4611686018427387904)) (PreH27 : (0 <= after)) (PreH28 : (after <= 4611686018427387904)) (PreH29 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cost_for_prime_safety_wit_42 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (i > 0)) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH3 : (cutFresh = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (v = (Znth i values 0))) (PreH17 : (2 <= v)) (PreH18 : (v <= 1000000000)) (PreH19 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 4611686018427387904)) (PreH22 : (0 <= keep)) (PreH23 : (keep <= 4611686018427387904)) (PreH24 : (0 <= cutFresh)) (PreH25 : (cutFresh <= 4611686018427387904)) (PreH26 : (0 <= cutAfterKeep)) (PreH27 : (cutAfterKeep <= 4611686018427387904)) (PreH28 : (0 <= after)) (PreH29 : (after <= 4611686018427387904)) (PreH30 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_43 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (i > 0)) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH3 : (cutFresh = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (v = (Znth i values 0))) (PreH17 : (2 <= v)) (PreH18 : (v <= 1000000000)) (PreH19 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 4611686018427387904)) (PreH22 : (0 <= keep)) (PreH23 : (keep <= 4611686018427387904)) (PreH24 : (0 <= cutFresh)) (PreH25 : (cutFresh <= 4611686018427387904)) (PreH26 : (0 <= cutAfterKeep)) (PreH27 : (cutAfterKeep <= 4611686018427387904)) (PreH28 : (0 <= after)) (PreH29 : (after <= 4611686018427387904)) (PreH30 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_44 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (i > 0)) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH3 : (cutFresh = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (v = (Znth i values 0))) (PreH17 : (2 <= v)) (PreH18 : (v <= 1000000000)) (PreH19 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 4611686018427387904)) (PreH22 : (0 <= keep)) (PreH23 : (keep <= 4611686018427387904)) (PreH24 : (0 <= cutFresh)) (PreH25 : (cutFresh <= 4611686018427387904)) (PreH26 : (0 <= cutAfterKeep)) (PreH27 : (cutAfterKeep <= 4611686018427387904)) (PreH28 : (0 <= after)) (PreH29 : (after <= 4611686018427387904)) (PreH30 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_45 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep <> (Z.shiftl 1 62))) (PreH2 : (i > 0)) (PreH3 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH4 : (cutFresh = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (2 <= p_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (v = (Znth i values 0))) (PreH18 : (2 <= v)) (PreH19 : (v <= 1000000000)) (PreH20 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH21 : (0 <= cost)) (PreH22 : (cost <= 4611686018427387904)) (PreH23 : (0 <= keep)) (PreH24 : (keep <= 4611686018427387904)) (PreH25 : (0 <= cutFresh)) (PreH26 : (cutFresh <= 4611686018427387904)) (PreH27 : (0 <= cutAfterKeep)) (PreH28 : (cutAfterKeep <= 4611686018427387904)) (PreH29 : (0 <= after)) (PreH30 : (after <= 4611686018427387904)) (PreH31 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ False ”
.

Definition cost_for_prime_safety_wit_46 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep = (Z.shiftl 1 62))) (PreH2 : (i > 0)) (PreH3 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH4 : (cutFresh = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (2 <= p_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (v = (Znth i values 0))) (PreH18 : (2 <= v)) (PreH19 : (v <= 1000000000)) (PreH20 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH21 : (0 <= cost)) (PreH22 : (cost <= 4611686018427387904)) (PreH23 : (0 <= keep)) (PreH24 : (keep <= 4611686018427387904)) (PreH25 : (0 <= cutFresh)) (PreH26 : (cutFresh <= 4611686018427387904)) (PreH27 : (0 <= cutAfterKeep)) (PreH28 : (cutAfterKeep <= 4611686018427387904)) (PreH29 : (0 <= after)) (PreH30 : (after <= 4611686018427387904)) (PreH31 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_47 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (i <= 0)) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH3 : (cutFresh = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (v = (Znth i values 0))) (PreH17 : (2 <= v)) (PreH18 : (v <= 1000000000)) (PreH19 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 4611686018427387904)) (PreH22 : (0 <= keep)) (PreH23 : (keep <= 4611686018427387904)) (PreH24 : (0 <= cutFresh)) (PreH25 : (cutFresh <= 4611686018427387904)) (PreH26 : (0 <= cutAfterKeep)) (PreH27 : (cutAfterKeep <= 4611686018427387904)) (PreH28 : (0 <= after)) (PreH29 : (after <= 4611686018427387904)) (PreH30 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_48 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (i <= 0)) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH3 : (cutFresh = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (v = (Znth i values 0))) (PreH17 : (2 <= v)) (PreH18 : (v <= 1000000000)) (PreH19 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 4611686018427387904)) (PreH22 : (0 <= keep)) (PreH23 : (keep <= 4611686018427387904)) (PreH24 : (0 <= cutFresh)) (PreH25 : (cutFresh <= 4611686018427387904)) (PreH26 : (0 <= cutAfterKeep)) (PreH27 : (cutAfterKeep <= 4611686018427387904)) (PreH28 : (0 <= after)) (PreH29 : (after <= 4611686018427387904)) (PreH30 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_49 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep = (Z.shiftl 1 62))) (PreH2 : (i > 0)) (PreH3 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH4 : (cutFresh = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (2 <= p_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (v = (Znth i values 0))) (PreH18 : (2 <= v)) (PreH19 : (v <= 1000000000)) (PreH20 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH21 : (0 <= cost)) (PreH22 : (cost <= 4611686018427387904)) (PreH23 : (0 <= keep)) (PreH24 : (keep <= 4611686018427387904)) (PreH25 : (0 <= cutFresh)) (PreH26 : (cutFresh <= 4611686018427387904)) (PreH27 : (0 <= cutAfterKeep)) (PreH28 : (cutAfterKeep <= 4611686018427387904)) (PreH29 : (0 <= after)) (PreH30 : (after <= 4611686018427387904)) (PreH31 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_50 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (i <= 0)) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH3 : (cutFresh = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (v = (Znth i values 0))) (PreH17 : (2 <= v)) (PreH18 : (v <= 1000000000)) (PreH19 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 4611686018427387904)) (PreH22 : (0 <= keep)) (PreH23 : (keep <= 4611686018427387904)) (PreH24 : (0 <= cutFresh)) (PreH25 : (cutFresh <= 4611686018427387904)) (PreH26 : (0 <= cutAfterKeep)) (PreH27 : (cutAfterKeep <= 4611686018427387904)) (PreH28 : (0 <= after)) (PreH29 : (after <= 4611686018427387904)) (PreH30 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_51 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep = (Z.shiftl 1 62))) (PreH2 : (i > 0)) (PreH3 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH4 : (cutFresh = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (2 <= p_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (v = (Znth i values 0))) (PreH18 : (2 <= v)) (PreH19 : (v <= 1000000000)) (PreH20 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH21 : (0 <= cost)) (PreH22 : (cost <= 4611686018427387904)) (PreH23 : (0 <= keep)) (PreH24 : (keep <= 4611686018427387904)) (PreH25 : (0 <= cutFresh)) (PreH26 : (cutFresh <= 4611686018427387904)) (PreH27 : (0 <= cutAfterKeep)) (PreH28 : (cutAfterKeep <= 4611686018427387904)) (PreH29 : (0 <= after)) (PreH30 : (after <= 4611686018427387904)) (PreH31 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_52 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutAfterKeep <> (Z.shiftl 1 62))) (PreH2 : (i <= 0)) (PreH3 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH4 : (cutFresh = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (2 <= p_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (v = (Znth i values 0))) (PreH18 : (2 <= v)) (PreH19 : (v <= 1000000000)) (PreH20 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH21 : (0 <= cost)) (PreH22 : (cost <= 4611686018427387904)) (PreH23 : (0 <= keep)) (PreH24 : (keep <= 4611686018427387904)) (PreH25 : (0 <= cutFresh)) (PreH26 : (cutFresh <= 4611686018427387904)) (PreH27 : (0 <= cutAfterKeep)) (PreH28 : (cutAfterKeep <= 4611686018427387904)) (PreH29 : (0 <= after)) (PreH30 : (after <= 4611686018427387904)) (PreH31 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ False ”
.

Definition cost_for_prime_safety_wit_53 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutAfterKeep <> (Z.shiftl 1 62))) (PreH2 : (keep = (Z.shiftl 1 62))) (PreH3 : (i > 0)) (PreH4 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ False ”
.

Definition cost_for_prime_safety_wit_54 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutFresh < cutAfterKeep)) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))) = (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "best_prev_cut" ) )) # Int64  |->_)
  **  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ False ”
.

Definition cost_for_prime_safety_wit_55 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min (cutFresh) (cutAfterKeep)) = (Z.min (cutFresh) (cutAfterKeep)))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nafter" ) )) # Int64  |->_)
  **  ((( &( "best_prev_cut" ) )) # Int64  |-> (Z.min (cutFresh) (cutAfterKeep)))
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_56 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min (cutFresh) (cutAfterKeep)) = (Z.min (cutFresh) (cutAfterKeep)))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nafter" ) )) # Int64  |->_)
  **  ((( &( "best_prev_cut" ) )) # Int64  |-> (Z.min (cutFresh) (cutAfterKeep)))
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_57 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min (cutFresh) (cutAfterKeep)) = (Z.min (cutFresh) (cutAfterKeep)))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nafter" ) )) # Int64  |->_)
  **  ((( &( "best_prev_cut" ) )) # Int64  |-> (Z.min (cutFresh) (cutAfterKeep)))
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_58 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min (cutFresh) (cutAfterKeep)) = (Z.min (cutFresh) (cutAfterKeep)))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nafter" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "best_prev_cut" ) )) # Int64  |-> (Z.min (cutFresh) (cutAfterKeep)))
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition cost_for_prime_safety_wit_59 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min (cutFresh) (cutAfterKeep)) = (Z.min (cutFresh) (cutAfterKeep)))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nafter" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "best_prev_cut" ) )) # Int64  |-> (Z.min (cutFresh) (cutAfterKeep)))
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition cost_for_prime_safety_wit_60 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min (cutFresh) (cutAfterKeep)) = (Z.min (cutFresh) (cutAfterKeep)))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nafter" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "best_prev_cut" ) )) # Int64  |-> (Z.min (cutFresh) (cutAfterKeep)))
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition cost_for_prime_safety_wit_61 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost <> (Z.shiftl 1 62))) (PreH2 : ((Z.min (cutFresh) (cutAfterKeep)) = (Z.min (cutFresh) (cutAfterKeep)))) (PreH3 : (cutFresh >= cutAfterKeep)) (PreH4 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (cutFresh = (Z.shiftl 1 62))) (PreH7 : (keep = (Z.shiftl 1 62))) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : (2 <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (v = (Znth i values 0))) (PreH20 : (2 <= v)) (PreH21 : (v <= 1000000000)) (PreH22 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH23 : (0 <= cost)) (PreH24 : (cost <= 4611686018427387904)) (PreH25 : (0 <= keep)) (PreH26 : (keep <= 4611686018427387904)) (PreH27 : (0 <= cutFresh)) (PreH28 : (cutFresh <= 4611686018427387904)) (PreH29 : (0 <= cutAfterKeep)) (PreH30 : (cutAfterKeep <= 4611686018427387904)) (PreH31 : (0 <= after)) (PreH32 : (after <= 4611686018427387904)) (PreH33 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nafter" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "best_prev_cut" ) )) # Int64  |-> (Z.min (cutFresh) (cutAfterKeep)))
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "cost" ) )) # Int64  |-> cost)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ False ”
.

Definition cost_for_prime_safety_wit_62 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost ))))) = (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost ))))))) (PreH2 : (cost = (Z.shiftl 1 62))) (PreH3 : (cutFresh >= cutAfterKeep)) (PreH4 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (cutFresh = (Z.shiftl 1 62))) (PreH7 : (keep = (Z.shiftl 1 62))) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : (2 <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (v = (Znth i values 0))) (PreH20 : (2 <= v)) (PreH21 : (v <= 1000000000)) (PreH22 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH23 : (0 <= cost)) (PreH24 : (cost <= 4611686018427387904)) (PreH25 : (0 <= keep)) (PreH26 : (keep <= 4611686018427387904)) (PreH27 : (0 <= cutFresh)) (PreH28 : (cutFresh <= 4611686018427387904)) (PreH29 : (0 <= cutAfterKeep)) (PreH30 : (cutAfterKeep <= 4611686018427387904)) (PreH31 : (0 <= after)) (PreH32 : (after <= 4611686018427387904)) (PreH33 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "after" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost ))))))
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "cutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "keep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition cost_for_prime_safety_wit_63 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (after < keep)) (PreH2 : (i >= n_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= keep)) (PreH15 : (keep <= 4611686018427387904)) (PreH16 : (0 <= cutFresh)) (PreH17 : (cutFresh <= 4611686018427387904)) (PreH18 : (0 <= cutAfterKeep)) (PreH19 : (cutAfterKeep <= 4611686018427387904)) (PreH20 : (0 <= after)) (PreH21 : (after <= 4611686018427387904)) (PreH22 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "best" ) )) # Int64  |-> keep)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ False ”
.

Definition cost_for_prime_safety_wit_64 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (cutAfterKeep < keep)) (PreH2 : (after >= keep)) (PreH3 : (i >= n_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= keep)) (PreH16 : (keep <= 4611686018427387904)) (PreH17 : (0 <= cutFresh)) (PreH18 : (cutFresh <= 4611686018427387904)) (PreH19 : (0 <= cutAfterKeep)) (PreH20 : (cutAfterKeep <= 4611686018427387904)) (PreH21 : (0 <= after)) (PreH22 : (after <= 4611686018427387904)) (PreH23 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "best" ) )) # Int64  |-> keep)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "p" ) )) # Int64  |-> p_pre)
  **  ((( &( "keep" ) )) # Int64  |-> keep)
  **  ((( &( "cutFresh" ) )) # Int64  |-> cutFresh)
  **  ((( &( "cutAfterKeep" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "after" ) )) # Int64  |-> after)
  **  (IntArray.full arr_pre n_pre values )
|--
  “ False ”
.

Definition cost_for_prime_entail_wit_1 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  (IntArray.full arr_pre n_pre values )
|--
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 4611686018427387904) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 4611686018427387904) ”
  &&  “ (0 <= (Z.shiftl 1 62)) ”
  &&  “ ((Z.shiftl 1 62) <= 4611686018427387904) ”
  &&  “ (0 <= (Z.shiftl 1 62)) ”
  &&  “ ((Z.shiftl 1 62) <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre 0 0 0 (Z.shiftl 1 62) (Z.shiftl 1 62) ) ”
  &&  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  TT && emp 
|--
  “ (CostForPrimeState values a_pre b_pre p_pre 0 0 0 (Z.shiftl 1 62) (Z.shiftl 1 62) ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  (CostForPrimeState values a_pre b_pre p_pre 0 0 0 (Z.shiftl 1 62) (Z.shiftl 1 62) )
.

Definition cost_for_prime_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (2 <= p_pre)),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition cost_for_prime_entail_wit_2_1 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (((Znth i values 0) % ( p_pre ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= keep)) (PreH15 : (keep <= 4611686018427387904)) (PreH16 : (0 <= cutFresh)) (PreH17 : (cutFresh <= 4611686018427387904)) (PreH18 : (0 <= cutAfterKeep)) (PreH19 : (cutAfterKeep <= 4611686018427387904)) (PreH20 : (0 <= after)) (PreH21 : (after <= 4611686018427387904)) (PreH22 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (IntArray.full arr_pre n_pre values )
|--
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i values 0) = (Znth i values 0)) ”
  &&  “ (2 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ (0 = (ElemCost (b_pre) (p_pre) ((Znth i values 0)))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (((Znth i values 0) % ( p_pre ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= keep)) (PreH15 : (keep <= 4611686018427387904)) (PreH16 : (0 <= cutFresh)) (PreH17 : (cutFresh <= 4611686018427387904)) (PreH18 : (0 <= cutAfterKeep)) (PreH19 : (cutAfterKeep <= 4611686018427387904)) (PreH20 : (0 <= after)) (PreH21 : (after <= 4611686018427387904)) (PreH22 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ (0 = (ElemCost (b_pre) (p_pre) ((Znth i values 0)))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_2_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (((Znth i values 0) % ( p_pre ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= keep)) (PreH15 : (keep <= 4611686018427387904)) (PreH16 : (0 <= cutFresh)) (PreH17 : (cutFresh <= 4611686018427387904)) (PreH18 : (0 <= cutAfterKeep)) (PreH19 : (cutAfterKeep <= 4611686018427387904)) (PreH20 : (0 <= after)) (PreH21 : (after <= 4611686018427387904)) (PreH22 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (0 = (ElemCost (b_pre) (p_pre) ((Znth i values 0))))
.

Definition cost_for_prime_entail_wit_2_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (((Znth i values 0) % ( p_pre ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= keep)) (PreH15 : (keep <= 4611686018427387904)) (PreH16 : (0 <= cutFresh)) (PreH17 : (cutFresh <= 4611686018427387904)) (PreH18 : (0 <= cutAfterKeep)) (PreH19 : (cutAfterKeep <= 4611686018427387904)) (PreH20 : (0 <= after)) (PreH21 : (after <= 4611686018427387904)) (PreH22 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition cost_for_prime_entail_wit_2_2 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) = 0)) (PreH2 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= keep)) (PreH16 : (keep <= 4611686018427387904)) (PreH17 : (0 <= cutFresh)) (PreH18 : (cutFresh <= 4611686018427387904)) (PreH19 : (0 <= cutAfterKeep)) (PreH20 : (cutAfterKeep <= 4611686018427387904)) (PreH21 : (0 <= after)) (PreH22 : (after <= 4611686018427387904)) (PreH23 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (IntArray.full arr_pre n_pre values )
|--
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i values 0) = (Znth i values 0)) ”
  &&  “ (2 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ (b_pre = (ElemCost (b_pre) (p_pre) ((Znth i values 0)))) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) = 0)) (PreH2 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= keep)) (PreH16 : (keep <= 4611686018427387904)) (PreH17 : (0 <= cutFresh)) (PreH18 : (cutFresh <= 4611686018427387904)) (PreH19 : (0 <= cutAfterKeep)) (PreH20 : (cutAfterKeep <= 4611686018427387904)) (PreH21 : (0 <= after)) (PreH22 : (after <= 4611686018427387904)) (PreH23 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ (b_pre = (ElemCost (b_pre) (p_pre) ((Znth i values 0)))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_2_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) = 0)) (PreH2 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= keep)) (PreH16 : (keep <= 4611686018427387904)) (PreH17 : (0 <= cutFresh)) (PreH18 : (cutFresh <= 4611686018427387904)) (PreH19 : (0 <= cutAfterKeep)) (PreH20 : (cutAfterKeep <= 4611686018427387904)) (PreH21 : (0 <= after)) (PreH22 : (after <= 4611686018427387904)) (PreH23 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (b_pre = (ElemCost (b_pre) (p_pre) ((Znth i values 0))))
.

Definition cost_for_prime_entail_wit_2_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) = 0)) (PreH2 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= keep)) (PreH16 : (keep <= 4611686018427387904)) (PreH17 : (0 <= cutFresh)) (PreH18 : (cutFresh <= 4611686018427387904)) (PreH19 : (0 <= cutAfterKeep)) (PreH20 : (cutAfterKeep <= 4611686018427387904)) (PreH21 : (0 <= after)) (PreH22 : (after <= 4611686018427387904)) (PreH23 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition cost_for_prime_entail_wit_2_3 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) = 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (IntArray.full arr_pre n_pre values )
|--
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i values 0) = (Znth i values 0)) ”
  &&  “ (2 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ (b_pre = (ElemCost (b_pre) (p_pre) ((Znth i values 0)))) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) = 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ (b_pre = (ElemCost (b_pre) (p_pre) ((Znth i values 0)))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_2_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) = 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (b_pre = (ElemCost (b_pre) (p_pre) ((Znth i values 0))))
.

Definition cost_for_prime_entail_wit_2_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) = 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition cost_for_prime_entail_wit_2_4 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) <> 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (IntArray.full arr_pre n_pre values )
|--
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i values 0) = (Znth i values 0)) ”
  &&  “ (2 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ ((Z.shiftl 1 62) = (ElemCost (b_pre) (p_pre) ((Znth i values 0)))) ”
  &&  “ (0 <= (Z.shiftl 1 62)) ”
  &&  “ ((Z.shiftl 1 62) <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) <> 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ ((Z.shiftl 1 62) = (ElemCost (b_pre) (p_pre) ((Znth i values 0)))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_2_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) <> 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.shiftl 1 62) = (ElemCost (b_pre) (p_pre) ((Znth i values 0))))
.

Definition cost_for_prime_entail_wit_2_4_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : ((((Znth i values 0) + 1 ) % ( p_pre ) ) <> 0)) (PreH2 : ((((Znth i values 0) - 1 ) % ( p_pre ) ) <> 0)) (PreH3 : (((Znth i values 0) % ( p_pre ) ) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH13 : (2 <= p_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= keep)) (PreH17 : (keep <= 4611686018427387904)) (PreH18 : (0 <= cutFresh)) (PreH19 : (cutFresh <= 4611686018427387904)) (PreH20 : (0 <= cutAfterKeep)) (PreH21 : (cutAfterKeep <= 4611686018427387904)) (PreH22 : (0 <= after)) (PreH23 : (after <= 4611686018427387904)) (PreH24 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition cost_for_prime_entail_wit_3 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep = (Z.shiftl 1 62))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (2 <= p_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (2 <= v)) (PreH15 : (v <= 1000000000)) (PreH16 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH17 : (0 <= cost)) (PreH18 : (cost <= 4611686018427387904)) (PreH19 : (0 <= keep)) (PreH20 : (keep <= 4611686018427387904)) (PreH21 : (0 <= cutFresh)) (PreH22 : (cutFresh <= 4611686018427387904)) (PreH23 : (0 <= cutAfterKeep)) (PreH24 : (cutAfterKeep <= 4611686018427387904)) (PreH25 : (0 <= after)) (PreH26 : (after <= 4611686018427387904)) (PreH27 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nkeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((Z.min ((Z.shiftl 1 62)) ((keep + cost ))) = (Z.min ((Z.shiftl 1 62)) ((keep + cost )))) ”
  &&  “ (keep = (Z.shiftl 1 62)) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (2 <= v) ”
  &&  “ (v <= 1000000000) ”
  &&  “ (cost = (ElemCost (b_pre) (p_pre) (v))) ”
  &&  “ (0 <= cost) ”
  &&  “ (cost <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep = (Z.shiftl 1 62))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (2 <= p_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (2 <= v)) (PreH15 : (v <= 1000000000)) (PreH16 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH17 : (0 <= cost)) (PreH18 : (cost <= 4611686018427387904)) (PreH19 : (0 <= keep)) (PreH20 : (keep <= 4611686018427387904)) (PreH21 : (0 <= cutFresh)) (PreH22 : (cutFresh <= 4611686018427387904)) (PreH23 : (0 <= cutAfterKeep)) (PreH24 : (cutAfterKeep <= 4611686018427387904)) (PreH25 : (0 <= after)) (PreH26 : (after <= 4611686018427387904)) (PreH27 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + cost )))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep = (Z.shiftl 1 62))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (2 <= p_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (2 <= v)) (PreH15 : (v <= 1000000000)) (PreH16 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH17 : (0 <= cost)) (PreH18 : (cost <= 4611686018427387904)) (PreH19 : (0 <= keep)) (PreH20 : (keep <= 4611686018427387904)) (PreH21 : (0 <= cutFresh)) (PreH22 : (cutFresh <= 4611686018427387904)) (PreH23 : (0 <= cutAfterKeep)) (PreH24 : (cutAfterKeep <= 4611686018427387904)) (PreH25 : (0 <= after)) (PreH26 : (after <= 4611686018427387904)) (PreH27 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + cost ))))
.

Definition cost_for_prime_entail_wit_4 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutFresh = (Z.shiftl 1 62))) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((keep + cost ))) = (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))) (PreH3 : (keep = (Z.shiftl 1 62))) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (v = (Znth i values 0))) (PreH16 : (2 <= v)) (PreH17 : (v <= 1000000000)) (PreH18 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH19 : (0 <= cost)) (PreH20 : (cost <= 4611686018427387904)) (PreH21 : (0 <= keep)) (PreH22 : (keep <= 4611686018427387904)) (PreH23 : (0 <= cutFresh)) (PreH24 : (cutFresh <= 4611686018427387904)) (PreH25 : (0 <= cutAfterKeep)) (PreH26 : (cutAfterKeep <= 4611686018427387904)) (PreH27 : (0 <= after)) (PreH28 : (after <= 4611686018427387904)) (PreH29 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre )))) ”
  &&  “ (cutFresh = (Z.shiftl 1 62)) ”
  &&  “ (keep = (Z.shiftl 1 62)) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (2 <= v) ”
  &&  “ (v <= 1000000000) ”
  &&  “ (cost = (ElemCost (b_pre) (p_pre) (v))) ”
  &&  “ (0 <= cost) ”
  &&  “ (cost <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutFresh = (Z.shiftl 1 62))) (PreH2 : (keep = (Z.shiftl 1 62))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (v = (Znth i values 0))) (PreH15 : (2 <= v)) (PreH16 : (v <= 1000000000)) (PreH17 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH18 : (0 <= cost)) (PreH19 : (cost <= 4611686018427387904)) (PreH20 : (0 <= keep)) (PreH21 : (keep <= 4611686018427387904)) (PreH22 : (0 <= cutFresh)) (PreH23 : (cutFresh <= 4611686018427387904)) (PreH24 : (0 <= cutAfterKeep)) (PreH25 : (cutAfterKeep <= 4611686018427387904)) (PreH26 : (0 <= after)) (PreH27 : (after <= 4611686018427387904)) (PreH28 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + a_pre )))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutFresh = (Z.shiftl 1 62))) (PreH2 : (keep = (Z.shiftl 1 62))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 1000000000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : (2 <= p_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (v = (Znth i values 0))) (PreH15 : (2 <= v)) (PreH16 : (v <= 1000000000)) (PreH17 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH18 : (0 <= cost)) (PreH19 : (cost <= 4611686018427387904)) (PreH20 : (0 <= keep)) (PreH21 : (keep <= 4611686018427387904)) (PreH22 : (0 <= cutFresh)) (PreH23 : (cutFresh <= 4611686018427387904)) (PreH24 : (0 <= cutAfterKeep)) (PreH25 : (cutAfterKeep <= 4611686018427387904)) (PreH26 : (0 <= after)) (PreH27 : (after <= 4611686018427387904)) (PreH28 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + a_pre ))))
.

Definition cost_for_prime_entail_wit_5_1 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH2 : (keep = (Z.shiftl 1 62))) (PreH3 : (i > 0)) (PreH4 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))) = (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) )))))))) ”
  &&  “ (cutAfterKeep = (Z.shiftl 1 62)) ”
  &&  “ (keep = (Z.shiftl 1 62)) ”
  &&  “ (cutFresh = (Z.shiftl 1 62)) ”
  &&  “ (keep = (Z.shiftl 1 62)) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (2 <= v) ”
  &&  “ (v <= 1000000000) ”
  &&  “ (cost = (ElemCost (b_pre) (p_pre) (v))) ”
  &&  “ (0 <= cost) ”
  &&  “ (cost <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep <= INT64_MAX)) (PreH2 : (keep >= INT64_MIN)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (i > 0)) (PreH6 : (cutFresh = (Z.shiftl 1 62))) (PreH7 : (keep = (Z.shiftl 1 62))) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : (2 <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (v = (Znth i values 0))) (PreH20 : (2 <= v)) (PreH21 : (v <= 1000000000)) (PreH22 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH23 : (0 <= cost)) (PreH24 : (cost <= 4611686018427387904)) (PreH25 : (0 <= keep)) (PreH26 : (keep <= 4611686018427387904)) (PreH27 : (0 <= cutFresh)) (PreH28 : (cutFresh <= 4611686018427387904)) (PreH29 : (0 <= cutAfterKeep)) (PreH30 : (cutAfterKeep <= 4611686018427387904)) (PreH31 : (0 <= after)) (PreH32 : (after <= 4611686018427387904)) (PreH33 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.shiftl 1 62) + a_pre )) ((Z.max (((Z.shiftl 1 62) + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) )))))))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_5_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep <= INT64_MAX)) (PreH2 : (keep >= INT64_MIN)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (i > 0)) (PreH6 : (cutFresh = (Z.shiftl 1 62))) (PreH7 : (keep = (Z.shiftl 1 62))) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : (2 <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (v = (Znth i values 0))) (PreH20 : (2 <= v)) (PreH21 : (v <= 1000000000)) (PreH22 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH23 : (0 <= cost)) (PreH24 : (cost <= 4611686018427387904)) (PreH25 : (0 <= keep)) (PreH26 : (keep <= 4611686018427387904)) (PreH27 : (0 <= cutFresh)) (PreH28 : (cutFresh <= 4611686018427387904)) (PreH29 : (0 <= cutAfterKeep)) (PreH30 : (cutAfterKeep <= 4611686018427387904)) (PreH31 : (0 <= after)) (PreH32 : (after <= 4611686018427387904)) (PreH33 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.shiftl 1 62) + a_pre )) ((Z.max (((Z.shiftl 1 62) + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
.

Definition cost_for_prime_entail_wit_5_2 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH2 : (i <= 0)) (PreH3 : ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) = (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))) (PreH4 : (cutFresh = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (2 <= p_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (v = (Znth i values 0))) (PreH18 : (2 <= v)) (PreH19 : (v <= 1000000000)) (PreH20 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH21 : (0 <= cost)) (PreH22 : (cost <= 4611686018427387904)) (PreH23 : (0 <= keep)) (PreH24 : (keep <= 4611686018427387904)) (PreH25 : (0 <= cutFresh)) (PreH26 : (cutFresh <= 4611686018427387904)) (PreH27 : (0 <= cutAfterKeep)) (PreH28 : (cutAfterKeep <= 4611686018427387904)) (PreH29 : (0 <= after)) (PreH30 : (after <= 4611686018427387904)) (PreH31 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))) = (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) )))))))) ”
  &&  “ (cutAfterKeep = (Z.shiftl 1 62)) ”
  &&  “ (keep = (Z.shiftl 1 62)) ”
  &&  “ (cutFresh = (Z.shiftl 1 62)) ”
  &&  “ (keep = (Z.shiftl 1 62)) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (2 <= v) ”
  &&  “ (v <= 1000000000) ”
  &&  “ (cost = (ElemCost (b_pre) (p_pre) (v))) ”
  &&  “ (0 <= cost) ”
  &&  “ (cost <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep <= INT64_MAX)) (PreH2 : (keep >= INT64_MIN)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (i <= 0)) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.shiftl 1 62) + a_pre )) ((Z.max (((Z.shiftl 1 62) + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) )))))))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_5_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep <= INT64_MAX)) (PreH2 : (keep >= INT64_MIN)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (i <= 0)) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.shiftl 1 62) + a_pre )) ((Z.max (((Z.shiftl 1 62) + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
.

Definition cost_for_prime_entail_wit_6 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cutFresh >= cutAfterKeep)) (PreH2 : ((Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))) = (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "best_prev_cut" ) )) # Int64  |-> cutAfterKeep)
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((Z.min (cutFresh) (cutAfterKeep)) = (Z.min (cutFresh) (cutAfterKeep))) ”
  &&  “ (cutFresh >= cutAfterKeep) ”
  &&  “ (cutAfterKeep = (Z.shiftl 1 62)) ”
  &&  “ (keep = (Z.shiftl 1 62)) ”
  &&  “ (cutFresh = (Z.shiftl 1 62)) ”
  &&  “ (keep = (Z.shiftl 1 62)) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (2 <= v) ”
  &&  “ (v <= 1000000000) ”
  &&  “ (cost = (ElemCost (b_pre) (p_pre) (v))) ”
  &&  “ (0 <= cost) ”
  &&  “ (cost <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  ((( &( "best_prev_cut" ) )) # Int64  |-> (Z.min (cutFresh) (cutAfterKeep)))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep <= INT64_MAX)) (PreH2 : (keep >= INT64_MIN)) (PreH3 : (cutFresh >= cutAfterKeep)) (PreH4 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (cutFresh = (Z.shiftl 1 62))) (PreH7 : (keep = (Z.shiftl 1 62))) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : (2 <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (v = (Znth i values 0))) (PreH20 : (2 <= v)) (PreH21 : (v <= 1000000000)) (PreH22 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH23 : (0 <= cost)) (PreH24 : (cost <= 4611686018427387904)) (PreH25 : (0 <= keep)) (PreH26 : (keep <= 4611686018427387904)) (PreH27 : (0 <= cutFresh)) (PreH28 : (cutFresh <= 4611686018427387904)) (PreH29 : (0 <= cutAfterKeep)) (PreH30 : (cutAfterKeep <= 4611686018427387904)) (PreH31 : (0 <= after)) (PreH32 : (after <= 4611686018427387904)) (PreH33 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) ((Z.shiftl 1 62)))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_6_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep <= INT64_MAX)) (PreH2 : (keep >= INT64_MIN)) (PreH3 : (cutFresh >= cutAfterKeep)) (PreH4 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (cutFresh = (Z.shiftl 1 62))) (PreH7 : (keep = (Z.shiftl 1 62))) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : (2 <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (v = (Znth i values 0))) (PreH20 : (2 <= v)) (PreH21 : (v <= 1000000000)) (PreH22 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH23 : (0 <= cost)) (PreH24 : (cost <= 4611686018427387904)) (PreH25 : (0 <= keep)) (PreH26 : (keep <= 4611686018427387904)) (PreH27 : (0 <= cutFresh)) (PreH28 : (cutFresh <= 4611686018427387904)) (PreH29 : (0 <= cutAfterKeep)) (PreH30 : (cutAfterKeep <= 4611686018427387904)) (PreH31 : (0 <= after)) (PreH32 : (after <= 4611686018427387904)) (PreH33 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) ((Z.shiftl 1 62))))
.

Definition cost_for_prime_entail_wit_7 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : ((Z.min (cutFresh) (cutAfterKeep)) = (Z.min (cutFresh) (cutAfterKeep)))) (PreH3 : (cutFresh >= cutAfterKeep)) (PreH4 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (cutFresh = (Z.shiftl 1 62))) (PreH7 : (keep = (Z.shiftl 1 62))) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : (2 <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (v = (Znth i values 0))) (PreH20 : (2 <= v)) (PreH21 : (v <= 1000000000)) (PreH22 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH23 : (0 <= cost)) (PreH24 : (cost <= 4611686018427387904)) (PreH25 : (0 <= keep)) (PreH26 : (keep <= 4611686018427387904)) (PreH27 : (0 <= cutFresh)) (PreH28 : (cutFresh <= 4611686018427387904)) (PreH29 : (0 <= cutAfterKeep)) (PreH30 : (cutAfterKeep <= 4611686018427387904)) (PreH31 : (0 <= after)) (PreH32 : (after <= 4611686018427387904)) (PreH33 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((( &( "nafter" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  (IntArray.full arr_pre n_pre values )
|--
  “ ((Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost ))))) = (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost )))))) ”
  &&  “ (cost = (Z.shiftl 1 62)) ”
  &&  “ (cutFresh >= cutAfterKeep) ”
  &&  “ (cutAfterKeep = (Z.shiftl 1 62)) ”
  &&  “ (keep = (Z.shiftl 1 62)) ”
  &&  “ (cutFresh = (Z.shiftl 1 62)) ”
  &&  “ (keep = (Z.shiftl 1 62)) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (2 <= v) ”
  &&  “ (v <= 1000000000) ”
  &&  “ (cost = (ElemCost (b_pre) (p_pre) (v))) ”
  &&  “ (0 <= cost) ”
  &&  “ (cost <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  ((( &( "nafter" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost ))))))
  **  ((( &( "ncutAfterKeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
  **  ((( &( "from" ) )) # Int64  |-> keep)
  **  ((( &( "ncutFresh" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))))
  **  ((( &( "nkeep" ) )) # Int64  |-> (Z.min ((Z.shiftl 1 62)) ((keep + cost ))))
  **  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep <= INT64_MAX)) (PreH2 : (keep >= INT64_MIN)) (PreH3 : (cost = (Z.shiftl 1 62))) (PreH4 : (cutFresh >= cutAfterKeep)) (PreH5 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (cutFresh = (Z.shiftl 1 62))) (PreH8 : (keep = (Z.shiftl 1 62))) (PreH9 : (0 <= a_pre)) (PreH10 : (a_pre <= 1000000000)) (PreH11 : (0 <= b_pre)) (PreH12 : (b_pre <= 1000000000)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 1000000)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH17 : (2 <= p_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (v = (Znth i values 0))) (PreH21 : (2 <= v)) (PreH22 : (v <= 1000000000)) (PreH23 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH24 : (0 <= cost)) (PreH25 : (cost <= 4611686018427387904)) (PreH26 : (0 <= keep)) (PreH27 : (keep <= 4611686018427387904)) (PreH28 : (0 <= cutFresh)) (PreH29 : (cutFresh <= 4611686018427387904)) (PreH30 : (0 <= cutAfterKeep)) (PreH31 : (cutAfterKeep <= 4611686018427387904)) (PreH32 : (0 <= after)) (PreH33 : (after <= 4611686018427387904)) (PreH34 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min ((Z.shiftl 1 62)) ((Z.shiftl 1 62))) + (Z.shiftl 1 62) )) ((after + (Z.shiftl 1 62) )))))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_7_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (keep <= INT64_MAX)) (PreH2 : (keep >= INT64_MIN)) (PreH3 : (cost = (Z.shiftl 1 62))) (PreH4 : (cutFresh >= cutAfterKeep)) (PreH5 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (cutFresh = (Z.shiftl 1 62))) (PreH8 : (keep = (Z.shiftl 1 62))) (PreH9 : (0 <= a_pre)) (PreH10 : (a_pre <= 1000000000)) (PreH11 : (0 <= b_pre)) (PreH12 : (b_pre <= 1000000000)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 1000000)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH17 : (2 <= p_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (v = (Znth i values 0))) (PreH21 : (2 <= v)) (PreH22 : (v <= 1000000000)) (PreH23 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH24 : (0 <= cost)) (PreH25 : (cost <= 4611686018427387904)) (PreH26 : (0 <= keep)) (PreH27 : (keep <= 4611686018427387904)) (PreH28 : (0 <= cutFresh)) (PreH29 : (cutFresh <= 4611686018427387904)) (PreH30 : (0 <= cutAfterKeep)) (PreH31 : (cutAfterKeep <= 4611686018427387904)) (PreH32 : (0 <= after)) (PreH33 : (after <= 4611686018427387904)) (PreH34 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.shiftl 1 62) = (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min ((Z.shiftl 1 62)) ((Z.shiftl 1 62))) + (Z.shiftl 1 62) )) ((after + (Z.shiftl 1 62) ))))))
.

Definition cost_for_prime_entail_wit_8 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : ((Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost ))))) = (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost ))))))) (PreH2 : (cost = (Z.shiftl 1 62))) (PreH3 : (cutFresh >= cutAfterKeep)) (PreH4 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH5 : (keep = (Z.shiftl 1 62))) (PreH6 : (cutFresh = (Z.shiftl 1 62))) (PreH7 : (keep = (Z.shiftl 1 62))) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH16 : (2 <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (v = (Znth i values 0))) (PreH20 : (2 <= v)) (PreH21 : (v <= 1000000000)) (PreH22 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH23 : (0 <= cost)) (PreH24 : (cost <= 4611686018427387904)) (PreH25 : (0 <= keep)) (PreH26 : (keep <= 4611686018427387904)) (PreH27 : (0 <= cutFresh)) (PreH28 : (cutFresh <= 4611686018427387904)) (PreH29 : (0 <= cutAfterKeep)) (PreH30 : (cutAfterKeep <= 4611686018427387904)) (PreH31 : (0 <= after)) (PreH32 : (after <= 4611686018427387904)) (PreH33 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (IntArray.full arr_pre n_pre values )
|--
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (Z.min ((Z.shiftl 1 62)) ((keep + cost )))) ”
  &&  “ ((Z.min ((Z.shiftl 1 62)) ((keep + cost ))) <= 4611686018427387904) ”
  &&  “ (0 <= (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre )))) ”
  &&  “ ((Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) <= 4611686018427387904) ”
  &&  “ (0 <= (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) )))))))) ”
  &&  “ ((Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))) <= 4611686018427387904) ”
  &&  “ (0 <= (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost )))))) ”
  &&  “ ((Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost ))))) <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre (i + 1 ) (Z.min ((Z.shiftl 1 62)) ((keep + cost ))) (Z.min ((Z.shiftl 1 62)) ((cutFresh + a_pre ))) (Z.min ((Z.shiftl 1 62)) ((Z.min ((cutAfterKeep + a_pre )) ((Z.max ((keep + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))) (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min (cutFresh) (cutAfterKeep)) + cost )) ((after + cost ))))) ) ”
  &&  (IntArray.full arr_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  TT && emp 
|--
  “ (CostForPrimeState values a_pre b_pre p_pre (i + 1 ) (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + (Z.shiftl 1 62) ))) (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + a_pre ))) (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.shiftl 1 62) + a_pre )) ((Z.max (((Z.shiftl 1 62) + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))) (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min ((Z.shiftl 1 62)) ((Z.shiftl 1 62))) + (Z.shiftl 1 62) )) ((after + (Z.shiftl 1 62) ))))) ) ”
  &&  “ ((Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min ((Z.shiftl 1 62)) ((Z.shiftl 1 62))) + (Z.shiftl 1 62) )) ((after + (Z.shiftl 1 62) ))))) <= 4611686018427387904) ”
  &&  “ (0 <= (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min ((Z.shiftl 1 62)) ((Z.shiftl 1 62))) + (Z.shiftl 1 62) )) ((after + (Z.shiftl 1 62) )))))) ”
  &&  “ ((Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.shiftl 1 62) + a_pre )) ((Z.max (((Z.shiftl 1 62) + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))) <= 4611686018427387904) ”
  &&  “ (0 <= (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.shiftl 1 62) + a_pre )) ((Z.max (((Z.shiftl 1 62) + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) )))))))) ”
  &&  “ ((Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + a_pre ))) <= 4611686018427387904) ”
  &&  “ (0 <= (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + a_pre )))) ”
  &&  “ ((Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + (Z.shiftl 1 62) ))) <= 4611686018427387904) ”
  &&  “ (0 <= (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + (Z.shiftl 1 62) )))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition cost_for_prime_entail_wit_8_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (CostForPrimeState values a_pre b_pre p_pre (i + 1 ) (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + (Z.shiftl 1 62) ))) (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + a_pre ))) (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.shiftl 1 62) + a_pre )) ((Z.max (((Z.shiftl 1 62) + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))) (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min ((Z.shiftl 1 62)) ((Z.shiftl 1 62))) + (Z.shiftl 1 62) )) ((after + (Z.shiftl 1 62) ))))) )
.

Definition cost_for_prime_entail_wit_8_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min ((Z.shiftl 1 62)) ((Z.shiftl 1 62))) + (Z.shiftl 1 62) )) ((after + (Z.shiftl 1 62) ))))) <= 4611686018427387904)
.

Definition cost_for_prime_entail_wit_8_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (0 <= (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.min ((Z.shiftl 1 62)) ((Z.shiftl 1 62))) + (Z.shiftl 1 62) )) ((after + (Z.shiftl 1 62) ))))))
.

Definition cost_for_prime_entail_wit_8_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.shiftl 1 62) + a_pre )) ((Z.max (((Z.shiftl 1 62) + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))) <= 4611686018427387904)
.

Definition cost_for_prime_entail_wit_8_split_goal_5 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (0 <= (Z.min ((Z.shiftl 1 62)) ((Z.min (((Z.shiftl 1 62) + a_pre )) ((Z.max (((Z.shiftl 1 62) + a_pre )) (((Z.shiftl 1 62) - (i * (Z.shiftl 1 62) ) ))))))))
.

Definition cost_for_prime_entail_wit_8_split_goal_6 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + a_pre ))) <= 4611686018427387904)
.

Definition cost_for_prime_entail_wit_8_split_goal_7 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (0 <= (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + a_pre ))))
.

Definition cost_for_prime_entail_wit_8_split_goal_8 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  ((Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + (Z.shiftl 1 62) ))) <= 4611686018427387904)
.

Definition cost_for_prime_entail_wit_8_split_goal_9 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (0 <= (Z.min ((Z.shiftl 1 62)) (((Z.shiftl 1 62) + (Z.shiftl 1 62) ))))
.

Definition cost_for_prime_entail_wit_8_split_goal_10 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (i: Z) (v: Z) (cost: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (PreH1 : (cost = (Z.shiftl 1 62))) (PreH2 : (cutFresh >= cutAfterKeep)) (PreH3 : (cutAfterKeep = (Z.shiftl 1 62))) (PreH4 : (keep = (Z.shiftl 1 62))) (PreH5 : (cutFresh = (Z.shiftl 1 62))) (PreH6 : (keep = (Z.shiftl 1 62))) (PreH7 : (0 <= a_pre)) (PreH8 : (a_pre <= 1000000000)) (PreH9 : (0 <= b_pre)) (PreH10 : (b_pre <= 1000000000)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 1000000)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((2 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH15 : (2 <= p_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (v = (Znth i values 0))) (PreH19 : (2 <= v)) (PreH20 : (v <= 1000000000)) (PreH21 : (cost = (ElemCost (b_pre) (p_pre) (v)))) (PreH22 : (0 <= cost)) (PreH23 : (cost <= 4611686018427387904)) (PreH24 : (0 <= keep)) (PreH25 : (keep <= 4611686018427387904)) (PreH26 : (0 <= cutFresh)) (PreH27 : (cutFresh <= 4611686018427387904)) (PreH28 : (0 <= cutAfterKeep)) (PreH29 : (cutAfterKeep <= 4611686018427387904)) (PreH30 : (0 <= after)) (PreH31 : (after <= 4611686018427387904)) (PreH32 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition cost_for_prime_entail_wit_9 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (cutAfterKeep >= keep)) (PreH2 : (after >= keep)) (PreH3 : (i >= n_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (2 <= p_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= keep)) (PreH16 : (keep <= 4611686018427387904)) (PreH17 : (0 <= cutFresh)) (PreH18 : (cutFresh <= 4611686018427387904)) (PreH19 : (0 <= cutAfterKeep)) (PreH20 : (cutAfterKeep <= 4611686018427387904)) (PreH21 : (0 <= after)) (PreH22 : (after <= 4611686018427387904)) (PreH23 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (IntArray.full arr_pre n_pre values )
|--
  (“ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (keep = 4611686018427387904) ”
  &&  “ (CostForPrime values a_pre b_pre p_pre keep ) ”
  &&  (IntArray.full arr_pre n_pre values ))
  ||
  (“ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 2000000000000000) ”
  &&  “ (CostForPrime values a_pre b_pre p_pre keep ) ”
  &&  (IntArray.full arr_pre n_pre values ))
.

Definition cost_for_prime_return_wit_1 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (0 <= keep)) (PreH5 : (keep <= 4611686018427387904)) (PreH6 : (0 <= cutFresh)) (PreH7 : (cutFresh <= 4611686018427387904)) (PreH8 : (0 <= cutAfterKeep)) (PreH9 : (cutAfterKeep <= 4611686018427387904)) (PreH10 : (0 <= after)) (PreH11 : (after <= 4611686018427387904)) (PreH12 : (best = 4611686018427387904)) (PreH13 : (CostForPrime values a_pre b_pre p_pre best )),
  (IntArray.full arr_pre n_pre values )
|--
  “ (CostForPrime values a_pre b_pre p_pre best ) ”
  &&  “ (best = 4611686018427387904) ”
  &&  (IntArray.full arr_pre n_pre values )
.

Definition cost_for_prime_return_wit_2 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (keep: Z) (cutFresh: Z) (cutAfterKeep: Z) (after: Z) (best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (0 <= keep)) (PreH5 : (keep <= 4611686018427387904)) (PreH6 : (0 <= cutFresh)) (PreH7 : (cutFresh <= 4611686018427387904)) (PreH8 : (0 <= cutAfterKeep)) (PreH9 : (cutAfterKeep <= 4611686018427387904)) (PreH10 : (0 <= after)) (PreH11 : (after <= 4611686018427387904)) (PreH12 : (0 <= best)) (PreH13 : (best <= 2000000000000000)) (PreH14 : (CostForPrime values a_pre b_pre p_pre best )),
  (IntArray.full arr_pre n_pre values )
|--
  “ (CostForPrime values a_pre b_pre p_pre best ) ”
  &&  “ (0 <= best) ”
  &&  “ (best <= 2000000000000000) ”
  &&  (IntArray.full arr_pre n_pre values )
.

Definition cost_for_prime_partial_solve_wit_1 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (p_pre: Z) (after: Z) (cutAfterKeep: Z) (cutFresh: Z) (keep: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (2 <= p_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= keep)) (PreH14 : (keep <= 4611686018427387904)) (PreH15 : (0 <= cutFresh)) (PreH16 : (cutFresh <= 4611686018427387904)) (PreH17 : (0 <= cutAfterKeep)) (PreH18 : (cutAfterKeep <= 4611686018427387904)) (PreH19 : (0 <= after)) (PreH20 : (after <= 4611686018427387904)) (PreH21 : (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after )),
  (IntArray.full arr_pre n_pre values )
|--
  “ (i < n_pre) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (2 <= p_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= keep) ”
  &&  “ (keep <= 4611686018427387904) ”
  &&  “ (0 <= cutFresh) ”
  &&  “ (cutFresh <= 4611686018427387904) ”
  &&  “ (0 <= cutAfterKeep) ”
  &&  “ (cutAfterKeep <= 4611686018427387904) ”
  &&  “ (0 <= after) ”
  &&  “ (after <= 4611686018427387904) ”
  &&  “ (CostForPrimeState values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after ) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre values )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))),
  ((( &( "nprime" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.full_shape primes_pre 256 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))),
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "nprime" ) )) # Int  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.full_shape primes_pre 256 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))),
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "nprime" ) )) # Int  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.full_shape primes_pre 256 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : ((-1) <= d)) (PreH10 : (d <= 2)) (PreH11 : (0 <= nprime)) (PreH12 : (nprime <= (60 * (d + 1 ) ))) (PreH13 : ((Zlength (ps)) = nprime)) (PreH14 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d <= 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  (IntArray.full arr_pre n_pre values )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (((Znth 0 values 0) + d ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth 0 values 0) + d )) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d <= 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (PreH1 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH2 : (0 <= (Zlength (fs)))) (PreH3 : ((Zlength (fs)) <= 30)) (PreH4 : (d <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : ((-1) <= d)) (PreH14 : (d <= 2)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= (60 * (d + 1 ) ))) (PreH17 : ((Zlength (ps)) = nprime)) (PreH18 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  (IntArray.full arr_pre n_pre values )
  **  ((( &( "nprime" ) )) # Int  |-> (nprime + (Zlength (fs)) ))
  **  (Int64Array.seg primes_pre 0 (nprime + (Zlength (fs)) ) (app (ps) (fs)) )
  **  (Int64Array.seg_shape primes_pre (nprime + (Zlength (fs)) ) 256 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (((Znth (n_pre - 1 ) values 0) + d ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (n_pre - 1 ) values 0) + d )) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (PreH1 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH2 : (0 <= (Zlength (fs)))) (PreH3 : ((Zlength (fs)) <= 30)) (PreH4 : (d <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : ((-1) <= d)) (PreH14 : (d <= 2)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= (60 * (d + 1 ) ))) (PreH17 : ((Zlength (ps)) = nprime)) (PreH18 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  ((( &( "nprime" ) )) # Int  |-> (nprime + (Zlength (fs)) ))
  **  (Int64Array.seg primes_pre 0 (nprime + (Zlength (fs)) ) (app (ps) (fs)) )
  **  (Int64Array.seg_shape primes_pre (nprime + (Zlength (fs)) ) 256 )
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (PreH1 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH2 : (0 <= (Zlength (fs)))) (PreH3 : ((Zlength (fs)) <= 30)) (PreH4 : (d <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : ((-1) <= d)) (PreH14 : (d <= 2)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= (60 * (d + 1 ) ))) (PreH17 : ((Zlength (ps)) = nprime)) (PreH18 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  ((( &( "nprime" ) )) # Int  |-> (nprime + (Zlength (fs)) ))
  **  (Int64Array.seg primes_pre 0 (nprime + (Zlength (fs)) ) (app (ps) (fs)) )
  **  (Int64Array.seg_shape primes_pre (nprime + (Zlength (fs)) ) 256 )
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (fs_2: (@list Z)) (PreH1 : (AddFactorsResult ((Znth (n_pre - 1 ) values 0) + d ) fs_2 )) (PreH2 : (0 <= (Zlength (fs_2)))) (PreH3 : ((Zlength (fs_2)) <= 30)) (PreH4 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH5 : (0 <= (Zlength (fs)))) (PreH6 : ((Zlength (fs)) <= 30)) (PreH7 : (d <= 1)) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : ((-1) <= d)) (PreH17 : (d <= 2)) (PreH18 : (0 <= nprime)) (PreH19 : (nprime <= (60 * (d + 1 ) ))) (PreH20 : ((Zlength (ps)) = nprime)) (PreH21 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  ((( &( "nprime" ) )) # Int  |-> ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) ))
  **  (Int64Array.seg primes_pre 0 ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) ) (app ((app (ps) (fs))) (fs_2)) )
  **  (Int64Array.seg_shape primes_pre ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) ) 256 )
  **  (IntArray.full arr_pre n_pre values )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ ((d + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d > 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  ((( &( "best" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ”
  &&  “ (62 <= 63) ”
  &&  “ (0 <= 62) ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d > 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  ((( &( "best" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (1 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d > 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  ((( &( "best" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d > 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (retval: Z) (PreH1 : (retval < best)) (PreH2 : (CostForPrime values a_pre b_pre (Znth (i - 0 ) ps 0) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 2000000000000000)) (PreH5 : (i < nprime)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (0 <= i)) (PreH15 : (i <= nprime)) (PreH16 : (0 <= nprime)) (PreH17 : (nprime <= 180)) (PreH18 : ((Zlength (ps)) = nprime)) (PreH19 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH20 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH21 : (0 <= best)) (PreH22 : (best <= 4611686018427387904)) (PreH23 : (BestPrefixCost values a_pre b_pre ps i best )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  ((( &( "r" ) )) # Int64  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  ((( &( "best" ) )) # Int64  |-> best)
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ False ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (retval: Z) (PreH1 : (retval < best)) (PreH2 : (CostForPrime values a_pre b_pre (Znth (i - 0 ) ps 0) retval )) (PreH3 : (retval = 4611686018427387904)) (PreH4 : (i < nprime)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (0 <= i)) (PreH14 : (i <= nprime)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= 180)) (PreH17 : ((Zlength (ps)) = nprime)) (PreH18 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH19 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH20 : (0 <= best)) (PreH21 : (best <= 4611686018427387904)) (PreH22 : (BestPrefixCost values a_pre b_pre ps i best )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  ((( &( "r" ) )) # Int64  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  ((( &( "best" ) )) # Int64  |-> best)
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ False ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (retval: Z) (PreH1 : (retval >= best)) (PreH2 : (CostForPrime values a_pre b_pre (Znth (i - 0 ) ps 0) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 2000000000000000)) (PreH5 : (i < nprime)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (0 <= i)) (PreH15 : (i <= nprime)) (PreH16 : (0 <= nprime)) (PreH17 : (nprime <= 180)) (PreH18 : ((Zlength (ps)) = nprime)) (PreH19 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH20 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH21 : (0 <= best)) (PreH22 : (best <= 4611686018427387904)) (PreH23 : (BestPrefixCost values a_pre b_pre ps i best )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  ((( &( "best" ) )) # Int64  |-> best)
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (retval: Z) (PreH1 : (retval >= best)) (PreH2 : (CostForPrime values a_pre b_pre (Znth (i - 0 ) ps 0) retval )) (PreH3 : (retval = 4611686018427387904)) (PreH4 : (i < nprime)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (0 <= i)) (PreH14 : (i <= nprime)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= 180)) (PreH17 : ((Zlength (ps)) = nprime)) (PreH18 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH19 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH20 : (0 <= best)) (PreH21 : (best <= 4611686018427387904)) (PreH22 : (BestPrefixCost values a_pre b_pre ps i best )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  ((( &( "best" ) )) # Int64  |-> best)
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.full_shape primes_pre 256 )
|--
  EX (ps: (@list Z)),
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ ((-1) <= (-1)) ”
  &&  “ ((-1) <= 2) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (60 * ((-1) + 1 ) )) ”
  &&  “ ((Zlength (ps)) = 0) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) (-1) ps ) ”
  &&  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 0 ps )
  **  (Int64Array.seg_shape primes_pre 0 256 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))),
  (Int64Array.full_shape primes_pre 256 )
|--
  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) (-1) (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  (Int64Array.seg_shape primes_pre 0 256 )
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))),
  (Int64Array.full_shape primes_pre 256 )
|--
  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) (-1) (@nil Z) ) ”
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))),
  (Int64Array.full_shape primes_pre 256 )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))),
  (Int64Array.full_shape primes_pre 256 )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
.

Definition solver_entail_wit_1_split_goal_spatial :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))),
  (Int64Array.full_shape primes_pre 256 )
|--
  (Int64Array.seg_shape primes_pre 0 256 )
.

Definition solver_entail_wit_2 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps_2: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (fs_2: (@list Z)) (PreH1 : (AddFactorsResult ((Znth (n_pre - 1 ) values 0) + d ) fs_2 )) (PreH2 : (0 <= (Zlength (fs_2)))) (PreH3 : ((Zlength (fs_2)) <= 30)) (PreH4 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH5 : (0 <= (Zlength (fs)))) (PreH6 : ((Zlength (fs)) <= 30)) (PreH7 : (d <= 1)) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : ((-1) <= d)) (PreH17 : (d <= 2)) (PreH18 : (0 <= nprime)) (PreH19 : (nprime <= (60 * (d + 1 ) ))) (PreH20 : ((Zlength (ps_2)) = nprime)) (PreH21 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps_2 )),
  (Int64Array.seg primes_pre 0 ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) ) (app ((app (ps_2) (fs))) (fs_2)) )
  **  (Int64Array.seg_shape primes_pre ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) ) 256 )
  **  (IntArray.full arr_pre n_pre values )
|--
  EX (ps: (@list Z)),
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ ((-1) <= (d + 1 )) ”
  &&  “ ((d + 1 ) <= 2) ”
  &&  “ (0 <= ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) )) ”
  &&  “ (((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) ) <= (60 * ((d + 1 ) + 1 ) )) ”
  &&  “ ((Zlength (ps)) = ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) )) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) (d + 1 ) ps ) ”
  &&  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) ) ps )
  **  (Int64Array.seg_shape primes_pre ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) ) 256 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (ps_2: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (fs_2: (@list Z)) (PreH1 : (AddFactorsResult ((Znth (n_pre - 1 ) values 0) + d ) fs_2 )) (PreH2 : (0 <= (Zlength (fs_2)))) (PreH3 : ((Zlength (fs_2)) <= 30)) (PreH4 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH5 : (0 <= (Zlength (fs)))) (PreH6 : ((Zlength (fs)) <= 30)) (PreH7 : (d <= 1)) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : ((-1) <= d)) (PreH17 : (d <= 2)) (PreH18 : (0 <= nprime)) (PreH19 : (nprime <= (60 * (d + 1 ) ))) (PreH20 : ((Zlength (ps_2)) = nprime)) (PreH21 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps_2 )),
  TT && emp 
|--
  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) (d + 1 ) (app ((app (ps_2) (fs))) (fs_2)) ) ”
  &&  “ ((Zlength ((app ((app (ps_2) (fs))) (fs_2)))) = ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (ps_2: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (fs_2: (@list Z)) (PreH1 : (AddFactorsResult ((Znth (n_pre - 1 ) values 0) + d ) fs_2 )) (PreH2 : (0 <= (Zlength (fs_2)))) (PreH3 : ((Zlength (fs_2)) <= 30)) (PreH4 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH5 : (0 <= (Zlength (fs)))) (PreH6 : ((Zlength (fs)) <= 30)) (PreH7 : (d <= 1)) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : ((-1) <= d)) (PreH17 : (d <= 2)) (PreH18 : (0 <= nprime)) (PreH19 : (nprime <= (60 * (d + 1 ) ))) (PreH20 : ((Zlength (ps_2)) = nprime)) (PreH21 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps_2 )),
  (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) (d + 1 ) (app ((app (ps_2) (fs))) (fs_2)) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (ps_2: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (fs_2: (@list Z)) (PreH1 : (AddFactorsResult ((Znth (n_pre - 1 ) values 0) + d ) fs_2 )) (PreH2 : (0 <= (Zlength (fs_2)))) (PreH3 : ((Zlength (fs_2)) <= 30)) (PreH4 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH5 : (0 <= (Zlength (fs)))) (PreH6 : ((Zlength (fs)) <= 30)) (PreH7 : (d <= 1)) (PreH8 : (0 <= a_pre)) (PreH9 : (a_pre <= 1000000000)) (PreH10 : (0 <= b_pre)) (PreH11 : (b_pre <= 1000000000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 1000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH16 : ((-1) <= d)) (PreH17 : (d <= 2)) (PreH18 : (0 <= nprime)) (PreH19 : (nprime <= (60 * (d + 1 ) ))) (PreH20 : ((Zlength (ps_2)) = nprime)) (PreH21 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps_2 )),
  ((Zlength ((app ((app (ps_2) (fs))) (fs_2)))) = ((nprime + (Zlength (fs)) ) + (Zlength (fs_2)) ))
.

Definition solver_entail_wit_3 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps_2: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d > 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < n_pre)) -> ((2 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps_2)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps_2 )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps_2 )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  EX (ps: (@list Z)),
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= nprime) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= 180) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0))) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps ) ”
  &&  “ (0 <= (Z.shiftl 1 62)) ”
  &&  “ ((Z.shiftl 1 62) <= 4611686018427387904) ”
  &&  “ (BestPrefixCost values a_pre b_pre ps 0 (Z.shiftl 1 62) ) ”
  &&  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (ps_2: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d > 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < n_pre)) -> ((2 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps_2)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps_2 )),
  TT && emp 
|--
  “ (BestPrefixCost values a_pre b_pre ps_2 0 (Z.shiftl 1 62) ) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps_2 ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps_2 0))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (ps_2: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d > 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < n_pre)) -> ((2 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps_2)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps_2 )),
  (BestPrefixCost values a_pre b_pre ps_2 0 (Z.shiftl 1 62) )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (ps_2: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d > 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < n_pre)) -> ((2 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps_2)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps_2 )),
  (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps_2 )
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (ps_2: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d > 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < n_pre)) -> ((2 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps_2)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps_2 )),
  forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps_2 0)))
.

Definition solver_entail_wit_3_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (ps_2: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d > 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < n_pre)) -> ((2 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps_2)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps_2 )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_4_1 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps_2: (@list Z)) (nprime: Z) (i: Z) (retval: Z) (PreH1 : (retval >= best)) (PreH2 : (CostForPrime values a_pre b_pre (Znth (i - 0 ) ps_2 0) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 2000000000000000)) (PreH5 : (i < nprime)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (0 <= i)) (PreH15 : (i <= nprime)) (PreH16 : (0 <= nprime)) (PreH17 : (nprime <= 180)) (PreH18 : ((Zlength (ps_2)) = nprime)) (PreH19 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps_2 0)))) (PreH20 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps_2 )) (PreH21 : (0 <= best)) (PreH22 : (best <= 4611686018427387904)) (PreH23 : (BestPrefixCost values a_pre b_pre ps_2 i best )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps_2 )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  EX (ps: (@list Z)),
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= nprime) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= 180) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0))) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps ) ”
  &&  “ (0 <= best) ”
  &&  “ (best <= 4611686018427387904) ”
  &&  “ (BestPrefixCost values a_pre b_pre ps (i + 1 ) best ) ”
  &&  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (best: Z) (ps_2: (@list Z)) (nprime: Z) (i: Z) (retval: Z) (PreH1 : (retval >= best)) (PreH2 : (CostForPrime values a_pre b_pre (Znth (i - 0 ) ps_2 0) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 2000000000000000)) (PreH5 : (i < nprime)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (0 <= i)) (PreH15 : (i <= nprime)) (PreH16 : (0 <= nprime)) (PreH17 : (nprime <= 180)) (PreH18 : ((Zlength (ps_2)) = nprime)) (PreH19 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps_2 0)))) (PreH20 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps_2 )) (PreH21 : (0 <= best)) (PreH22 : (best <= 4611686018427387904)) (PreH23 : (BestPrefixCost values a_pre b_pre ps_2 i best )),
  TT && emp 
|--
  “ (BestPrefixCost values a_pre b_pre ps_2 (i + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (best: Z) (ps_2: (@list Z)) (nprime: Z) (i: Z) (retval: Z) (PreH1 : (retval >= best)) (PreH2 : (CostForPrime values a_pre b_pre (Znth (i - 0 ) ps_2 0) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 2000000000000000)) (PreH5 : (i < nprime)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 1000000000)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 1000000000)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 1000000)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH14 : (0 <= i)) (PreH15 : (i <= nprime)) (PreH16 : (0 <= nprime)) (PreH17 : (nprime <= 180)) (PreH18 : ((Zlength (ps_2)) = nprime)) (PreH19 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps_2 0)))) (PreH20 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps_2 )) (PreH21 : (0 <= best)) (PreH22 : (best <= 4611686018427387904)) (PreH23 : (BestPrefixCost values a_pre b_pre ps_2 i best )),
  (BestPrefixCost values a_pre b_pre ps_2 (i + 1 ) best )
.

Definition solver_entail_wit_4_2 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps_2: (@list Z)) (nprime: Z) (i: Z) (retval: Z) (PreH1 : (retval >= best)) (PreH2 : (CostForPrime values a_pre b_pre (Znth (i - 0 ) ps_2 0) retval )) (PreH3 : (retval = 4611686018427387904)) (PreH4 : (i < nprime)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (0 <= i)) (PreH14 : (i <= nprime)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= 180)) (PreH17 : ((Zlength (ps_2)) = nprime)) (PreH18 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps_2 0)))) (PreH19 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps_2 )) (PreH20 : (0 <= best)) (PreH21 : (best <= 4611686018427387904)) (PreH22 : (BestPrefixCost values a_pre b_pre ps_2 i best )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps_2 )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  EX (ps: (@list Z)),
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= nprime) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= 180) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0))) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps ) ”
  &&  “ (0 <= best) ”
  &&  “ (best <= 4611686018427387904) ”
  &&  “ (BestPrefixCost values a_pre b_pre ps (i + 1 ) best ) ”
  &&  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (best: Z) (ps_2: (@list Z)) (nprime: Z) (i: Z) (retval: Z) (PreH1 : (retval >= best)) (PreH2 : (CostForPrime values a_pre b_pre (Znth (i - 0 ) ps_2 0) retval )) (PreH3 : (retval = 4611686018427387904)) (PreH4 : (i < nprime)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (0 <= i)) (PreH14 : (i <= nprime)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= 180)) (PreH17 : ((Zlength (ps_2)) = nprime)) (PreH18 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps_2 0)))) (PreH19 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps_2 )) (PreH20 : (0 <= best)) (PreH21 : (best <= 4611686018427387904)) (PreH22 : (BestPrefixCost values a_pre b_pre ps_2 i best )),
  TT && emp 
|--
  “ (BestPrefixCost values a_pre b_pre ps_2 (i + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (best: Z) (ps_2: (@list Z)) (nprime: Z) (i: Z) (retval: Z) (PreH1 : (retval >= best)) (PreH2 : (CostForPrime values a_pre b_pre (Znth (i - 0 ) ps_2 0) retval )) (PreH3 : (retval = 4611686018427387904)) (PreH4 : (i < nprime)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : (0 <= i)) (PreH14 : (i <= nprime)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= 180)) (PreH17 : ((Zlength (ps_2)) = nprime)) (PreH18 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps_2 0)))) (PreH19 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps_2 )) (PreH20 : (0 <= best)) (PreH21 : (best <= 4611686018427387904)) (PreH22 : (BestPrefixCost values a_pre b_pre ps_2 i best )),
  (BestPrefixCost values a_pre b_pre ps_2 (i + 1 ) best )
.

Definition solver_entail_wit_5 :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (PreH1 : (0 <= nprime)) (PreH2 : (nprime <= 256)) (PreH3 : (i >= nprime)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= nprime)) (PreH14 : (0 <= nprime)) (PreH15 : (nprime <= 180)) (PreH16 : ((Zlength (ps)) = nprime)) (PreH17 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH18 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH19 : (0 <= best)) (PreH20 : (best <= 4611686018427387904)) (PreH21 : (BestPrefixCost values a_pre b_pre ps i best )),
  (Int64Array.full_shape primes_pre 256 )
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= 180) ”
  &&  “ (Spec a_pre b_pre values best ) ”
  &&  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.full_shape primes_pre 256 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (PreH1 : (0 <= nprime)) (PreH2 : (nprime <= 256)) (PreH3 : (i >= nprime)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= nprime)) (PreH14 : (0 <= nprime)) (PreH15 : (nprime <= 180)) (PreH16 : ((Zlength (ps)) = nprime)) (PreH17 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH18 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH19 : (0 <= best)) (PreH20 : (best <= 4611686018427387904)) (PreH21 : (BestPrefixCost values a_pre b_pre ps i best )),
  TT && emp 
|--
  “ (Spec a_pre b_pre values best ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (a_pre: Z) (b_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (PreH1 : (0 <= nprime)) (PreH2 : (nprime <= 256)) (PreH3 : (i >= nprime)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 1000000000)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 1000000000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 1000000)) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= nprime)) (PreH14 : (0 <= nprime)) (PreH15 : (nprime <= 180)) (PreH16 : ((Zlength (ps)) = nprime)) (PreH17 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH18 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH19 : (0 <= best)) (PreH20 : (best <= 4611686018427387904)) (PreH21 : (BestPrefixCost values a_pre b_pre ps i best )),
  (Spec a_pre b_pre values best )
.

Definition solver_return_wit_1 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (nprime: Z) (best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (0 <= nprime)) (PreH5 : (nprime <= 180)) (PreH6 : (Spec a_pre b_pre values best )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.full_shape primes_pre 256 )
|--
  “ (Spec a_pre b_pre values best ) ”
  &&  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.full_shape primes_pre 256 )
.

Definition solver_partial_solve_wit_1 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d <= 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (d <= 1) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ ((-1) <= d) ”
  &&  “ (d <= 2) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= (60 * (d + 1 ) )) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps ) ”
  &&  (((arr_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 values 0))
  **  (IntArray.missing_i arr_pre 0 0 n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
.

Definition solver_partial_solve_wit_2_pure :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d <= 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  (IntArray.full arr_pre n_pre values )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (((Znth 0 values 0) + d ) = ((Znth 0 values 0) + d )) ”
  &&  “ (1 <= ((Znth 0 values 0) + d )) ”
  &&  “ (((Znth 0 values 0) + d ) <= 1000000001) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= 200) ”
  &&  “ ((Zlength (ps)) = nprime) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (PreH1 : (d <= 1)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : ((-1) <= d)) (PreH11 : (d <= 2)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= (60 * (d + 1 ) ))) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (((Znth 0 values 0) + d ) = ((Znth 0 values 0) + d )) ”
  &&  “ (1 <= ((Znth 0 values 0) + d )) ”
  &&  “ (((Znth 0 values 0) + d ) <= 1000000001) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= 200) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ (d <= 1) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ ((-1) <= d) ”
  &&  “ (d <= 2) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= (60 * (d + 1 ) )) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps ) ”
  &&  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
  **  (IntArray.full arr_pre n_pre values )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (PreH1 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH2 : (0 <= (Zlength (fs)))) (PreH3 : ((Zlength (fs)) <= 30)) (PreH4 : (d <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : ((-1) <= d)) (PreH14 : (d <= 2)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= (60 * (d + 1 ) ))) (PreH17 : ((Zlength (ps)) = nprime)) (PreH18 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  (Int64Array.seg primes_pre 0 (nprime + (Zlength (fs)) ) (app (ps) (fs)) )
  **  (Int64Array.seg_shape primes_pre (nprime + (Zlength (fs)) ) 256 )
  **  (IntArray.full arr_pre n_pre values )
|--
  “ (AddFactorsResult ((Znth 0 values 0) + d ) fs ) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  “ (d <= 1) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ ((-1) <= d) ”
  &&  “ (d <= 2) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= (60 * (d + 1 ) )) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps ) ”
  &&  (((arr_pre + ((n_pre - 1 ) * sizeof(INT)))) # Int  |-> (Znth (n_pre - 1 ) values 0))
  **  (IntArray.missing_i arr_pre (n_pre - 1 ) 0 n_pre values )
  **  (Int64Array.seg primes_pre 0 (nprime + (Zlength (fs)) ) (app (ps) (fs)) )
  **  (Int64Array.seg_shape primes_pre (nprime + (Zlength (fs)) ) 256 )
.

Definition solver_partial_solve_wit_4_pure :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (PreH1 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH2 : (0 <= (Zlength (fs)))) (PreH3 : ((Zlength (fs)) <= 30)) (PreH4 : (d <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : ((-1) <= d)) (PreH14 : (d <= 2)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= (60 * (d + 1 ) ))) (PreH17 : ((Zlength (ps)) = nprime)) (PreH18 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  (IntArray.full arr_pre n_pre values )
  **  ((( &( "nprime" ) )) # Int  |-> (nprime + (Zlength (fs)) ))
  **  (Int64Array.seg primes_pre 0 (nprime + (Zlength (fs)) ) (app (ps) (fs)) )
  **  (Int64Array.seg_shape primes_pre (nprime + (Zlength (fs)) ) 256 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (((Znth (n_pre - 1 ) values 0) + d ) = ((Znth (n_pre - 1 ) values 0) + d )) ”
  &&  “ (1 <= ((Znth (n_pre - 1 ) values 0) + d )) ”
  &&  “ (((Znth (n_pre - 1 ) values 0) + d ) <= 1000000001) ”
  &&  “ (0 <= (nprime + (Zlength (fs)) )) ”
  &&  “ ((nprime + (Zlength (fs)) ) <= 200) ”
  &&  “ ((Zlength ((app (ps) (fs)))) = (nprime + (Zlength (fs)) )) ”
) \/
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (PreH1 : (b_pre <= INT64_MAX)) (PreH2 : (a_pre <= INT64_MAX)) (PreH3 : (b_pre >= INT64_MIN)) (PreH4 : (a_pre >= INT64_MIN)) (PreH5 : (d <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((nprime + (Zlength (fs)) ) <= INT_MAX)) (PreH8 : (d >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((nprime + (Zlength (fs)) ) >= INT_MIN)) (PreH11 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH12 : (0 <= (Zlength (fs)))) (PreH13 : ((Zlength (fs)) <= 30)) (PreH14 : (d <= 1)) (PreH15 : (0 <= a_pre)) (PreH16 : (a_pre <= 1000000000)) (PreH17 : (0 <= b_pre)) (PreH18 : (b_pre <= 1000000000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 1000000)) (PreH21 : (n_pre = (Zlength (values)))) (PreH22 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH23 : ((-1) <= d)) (PreH24 : (d <= 2)) (PreH25 : (0 <= nprime)) (PreH26 : (nprime <= (60 * (d + 1 ) ))) (PreH27 : ((Zlength (ps)) = nprime)) (PreH28 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  (IntArray.full arr_pre n_pre values )
  **  ((( &( "nprime" ) )) # Int  |-> (nprime + (Zlength (fs)) ))
  **  (Int64Array.seg primes_pre 0 (nprime + (Zlength (fs)) ) (app (ps) (fs)) )
  **  (Int64Array.seg_shape primes_pre (nprime + (Zlength (fs)) ) 256 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ ((Zlength ((app (ps) (fs)))) = (nprime + (Zlength (fs)) )) ”
).

Definition solver_partial_solve_wit_4_pure_split_goal_1 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (PreH1 : (b_pre <= INT64_MAX)) (PreH2 : (a_pre <= INT64_MAX)) (PreH3 : (b_pre >= INT64_MIN)) (PreH4 : (a_pre >= INT64_MIN)) (PreH5 : (d <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((nprime + (Zlength (fs)) ) <= INT_MAX)) (PreH8 : (d >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((nprime + (Zlength (fs)) ) >= INT_MIN)) (PreH11 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH12 : (0 <= (Zlength (fs)))) (PreH13 : ((Zlength (fs)) <= 30)) (PreH14 : (d <= 1)) (PreH15 : (0 <= a_pre)) (PreH16 : (a_pre <= 1000000000)) (PreH17 : (0 <= b_pre)) (PreH18 : (b_pre <= 1000000000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 1000000)) (PreH21 : (n_pre = (Zlength (values)))) (PreH22 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH23 : ((-1) <= d)) (PreH24 : (d <= 2)) (PreH25 : (0 <= nprime)) (PreH26 : (nprime <= (60 * (d + 1 ) ))) (PreH27 : ((Zlength (ps)) = nprime)) (PreH28 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  (IntArray.full arr_pre n_pre values )
  **  ((( &( "nprime" ) )) # Int  |-> (nprime + (Zlength (fs)) ))
  **  (Int64Array.seg primes_pre 0 (nprime + (Zlength (fs)) ) (app (ps) (fs)) )
  **  (Int64Array.seg_shape primes_pre (nprime + (Zlength (fs)) ) 256 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ ((Zlength ((app (ps) (fs)))) = (nprime + (Zlength (fs)) )) ”
.

Definition solver_partial_solve_wit_4_aux :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (ps: (@list Z)) (nprime: Z) (d: Z) (fs: (@list Z)) (PreH1 : (AddFactorsResult ((Znth 0 values 0) + d ) fs )) (PreH2 : (0 <= (Zlength (fs)))) (PreH3 : ((Zlength (fs)) <= 30)) (PreH4 : (d <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 1000000000)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 1000000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 1000000)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH13 : ((-1) <= d)) (PreH14 : (d <= 2)) (PreH15 : (0 <= nprime)) (PreH16 : (nprime <= (60 * (d + 1 ) ))) (PreH17 : ((Zlength (ps)) = nprime)) (PreH18 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 (nprime + (Zlength (fs)) ) (app (ps) (fs)) )
  **  (Int64Array.seg_shape primes_pre (nprime + (Zlength (fs)) ) 256 )
|--
  “ (((Znth (n_pre - 1 ) values 0) + d ) = ((Znth (n_pre - 1 ) values 0) + d )) ”
  &&  “ (1 <= ((Znth (n_pre - 1 ) values 0) + d )) ”
  &&  “ (((Znth (n_pre - 1 ) values 0) + d ) <= 1000000001) ”
  &&  “ (0 <= (nprime + (Zlength (fs)) )) ”
  &&  “ ((nprime + (Zlength (fs)) ) <= 200) ”
  &&  “ ((Zlength ((app (ps) (fs)))) = (nprime + (Zlength (fs)) )) ”
  &&  “ (AddFactorsResult ((Znth 0 values 0) + d ) fs ) ”
  &&  “ (0 <= (Zlength (fs))) ”
  &&  “ ((Zlength (fs)) <= 30) ”
  &&  “ (d <= 1) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ ((-1) <= d) ”
  &&  “ (d <= 2) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= (60 * (d + 1 ) )) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) d ps ) ”
  &&  (Int64Array.seg primes_pre 0 (nprime + (Zlength (fs)) ) (app (ps) (fs)) )
  **  (Int64Array.seg_shape primes_pre (nprime + (Zlength (fs)) ) 256 )
  **  (IntArray.full arr_pre n_pre values )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (PreH1 : (i < nprime)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= nprime)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= 180)) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH16 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH17 : (0 <= best)) (PreH18 : (best <= 4611686018427387904)) (PreH19 : (BestPrefixCost values a_pre b_pre ps i best )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (i < nprime) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nprime) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= 180) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0))) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps ) ”
  &&  “ (0 <= best) ”
  &&  “ (best <= 4611686018427387904) ”
  &&  “ (BestPrefixCost values a_pre b_pre ps i best ) ”
  &&  (((primes_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) ps 0))
  **  (Int64Array.missing_i primes_pre i 0 nprime ps )
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
.

Definition solver_partial_solve_wit_6_pure :=
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (PreH1 : (i < nprime)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= nprime)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= 180)) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH16 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH17 : (0 <= best)) (PreH18 : (best <= 4611686018427387904)) (PreH19 : (BestPrefixCost values a_pre b_pre ps i best )),
  (Int64Array.seg primes_pre 0 nprime ps )
  **  ((( &( "r" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  ((( &( "best" ) )) # Int64  |-> best)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= (Znth (i - 0 ) ps 0)) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((2 <= (Znth i_2 values 0)) /\ ((Znth i_2 values 0) <= 1000000000))) ”
) \/
(
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (PreH1 : (best <= INT64_MAX)) (PreH2 : (b_pre <= INT64_MAX)) (PreH3 : (a_pre <= INT64_MAX)) (PreH4 : (best >= INT64_MIN)) (PreH5 : (b_pre >= INT64_MIN)) (PreH6 : (a_pre >= INT64_MIN)) (PreH7 : (nprime <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (nprime >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (i < nprime)) (PreH14 : (0 <= a_pre)) (PreH15 : (a_pre <= 1000000000)) (PreH16 : (0 <= b_pre)) (PreH17 : (b_pre <= 1000000000)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 1000000)) (PreH20 : (n_pre = (Zlength (values)))) (PreH21 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : (0 <= i)) (PreH23 : (i <= nprime)) (PreH24 : (0 <= nprime)) (PreH25 : (nprime <= 180)) (PreH26 : ((Zlength (ps)) = nprime)) (PreH27 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH28 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH29 : (0 <= best)) (PreH30 : (best <= 4611686018427387904)) (PreH31 : (BestPrefixCost values a_pre b_pre ps i best )),
  (Int64Array.seg primes_pre 0 nprime ps )
  **  ((( &( "r" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  ((( &( "best" ) )) # Int64  |-> best)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((2 <= (Znth i_2 values 0)) /\ ((Znth i_2 values 0) <= 1000000000))) ”
).

Definition solver_partial_solve_wit_6_pure_split_goal_1 :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (PreH1 : (best <= INT64_MAX)) (PreH2 : (b_pre <= INT64_MAX)) (PreH3 : (a_pre <= INT64_MAX)) (PreH4 : (best >= INT64_MIN)) (PreH5 : (b_pre >= INT64_MIN)) (PreH6 : (a_pre >= INT64_MIN)) (PreH7 : (nprime <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (nprime >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (i < nprime)) (PreH14 : (0 <= a_pre)) (PreH15 : (a_pre <= 1000000000)) (PreH16 : (0 <= b_pre)) (PreH17 : (b_pre <= 1000000000)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 1000000)) (PreH20 : (n_pre = (Zlength (values)))) (PreH21 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : (0 <= i)) (PreH23 : (i <= nprime)) (PreH24 : (0 <= nprime)) (PreH25 : (nprime <= 180)) (PreH26 : ((Zlength (ps)) = nprime)) (PreH27 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH28 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH29 : (0 <= best)) (PreH30 : (best <= 4611686018427387904)) (PreH31 : (BestPrefixCost values a_pre b_pre ps i best )),
  (Int64Array.seg primes_pre 0 nprime ps )
  **  ((( &( "r" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  ((( &( "best" ) )) # Int64  |-> best)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((2 <= (Znth i_2 values 0)) /\ ((Znth i_2 values 0) <= 1000000000))) ”
.

Definition solver_partial_solve_wit_6_aux :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (PreH1 : (i < nprime)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= nprime)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= 180)) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH16 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH17 : (0 <= best)) (PreH18 : (best <= 4611686018427387904)) (PreH19 : (BestPrefixCost values a_pre b_pre ps i best )),
  (Int64Array.seg primes_pre 0 nprime ps )
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= (Znth (i - 0 ) ps 0)) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((2 <= (Znth i_2 values 0)) /\ ((Znth i_2 values 0) <= 1000000000))) ”
  &&  “ (i < nprime) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nprime) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= 180) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0))) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps ) ”
  &&  “ (0 <= best) ”
  &&  “ (best <= 4611686018427387904) ”
  &&  “ (BestPrefixCost values a_pre b_pre ps i best ) ”
  &&  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
.

Definition solver_partial_solve_wit_6 := solver_partial_solve_wit_6_pure -> solver_partial_solve_wit_6_aux.

Definition solver_partial_solve_wit_7_pure :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (PreH1 : (i >= nprime)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= nprime)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= 180)) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH16 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH17 : (0 <= best)) (PreH18 : (best <= 4611686018427387904)) (PreH19 : (BestPrefixCost values a_pre b_pre ps i best )),
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
  **  ((( &( "primes" ) )) # Ptr  |-> primes_pre)
  **  ((( &( "nprime" ) )) # Int  |-> nprime)
  **  ((( &( "best" ) )) # Int64  |-> best)
  **  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (0 <= nprime) ”
  &&  “ (nprime <= 256) ”
.

Definition solver_partial_solve_wit_7_aux :=
forall (values: (@list Z)) (arr_pre: Z) (n_pre: Z) (a_pre: Z) (b_pre: Z) (primes_pre: Z) (best: Z) (ps: (@list Z)) (nprime: Z) (i: Z) (PreH1 : (i >= nprime)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 1000000000)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 1000000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= nprime)) (PreH12 : (0 <= nprime)) (PreH13 : (nprime <= 180)) (PreH14 : ((Zlength (ps)) = nprime)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0)))) (PreH16 : (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps )) (PreH17 : (0 <= best)) (PreH18 : (best <= 4611686018427387904)) (PreH19 : (BestPrefixCost values a_pre b_pre ps i best )),
  (IntArray.full arr_pre n_pre values )
  **  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
|--
  “ (0 <= nprime) ”
  &&  “ (nprime <= 256) ”
  &&  “ (i >= nprime) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nprime) ”
  &&  “ (0 <= nprime) ”
  &&  “ (nprime <= 180) ”
  &&  “ ((Zlength (ps)) = nprime) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nprime)) -> (2 <= (Znth j_2 ps 0))) ”
  &&  “ (CandidateCoverage (Znth 0 values 0) (Znth (n_pre - 1 ) values 0) 2 ps ) ”
  &&  “ (0 <= best) ”
  &&  “ (best <= 4611686018427387904) ”
  &&  “ (BestPrefixCost values a_pre b_pre ps i best ) ”
  &&  (Int64Array.seg primes_pre 0 nprime ps )
  **  (Int64Array.seg_shape primes_pre nprime 256 )
  **  (IntArray.full arr_pre n_pre values )
.

Definition solver_partial_solve_wit_7 := solver_partial_solve_wit_7_pure -> solver_partial_solve_wit_7_aux.

Definition solver_which_implies_wit_1 :=
(
forall (ps: (@list Z)) (nprime: Z) (primes: Z) (PreH1 : (0 <= nprime)) (PreH2 : (nprime <= 256)),
  (Int64Array.seg primes 0 nprime ps )
  **  (Int64Array.seg_shape primes nprime 256 )
|--
  “ (0 <= nprime) ”
  &&  “ (nprime <= 256) ”
  &&  (Int64Array.full_shape primes 256 )
) \/
(
forall (ps: (@list Z)) (nprime: Z) (primes: Z) (PreH1 : (0 <= nprime)) (PreH2 : (nprime <= 256)),
  (Int64Array.seg primes 0 nprime ps )
  **  (Int64Array.seg_shape primes nprime 256 )
|--
  (Int64Array.full_shape primes 256 )
).

Definition solver_which_implies_wit_1_split_goal_spatial :=
forall (ps: (@list Z)) (nprime: Z) (primes: Z) (PreH1 : (0 <= nprime)) (PreH2 : (nprime <= 256)),
  (Int64Array.seg primes 0 nprime ps )
  **  (Int64Array.seg_shape primes nprime 256 )
|--
  (Int64Array.full_shape primes 256 )
.

Module Type VC_Correct.


Axiom proof_of_add_factors_safety_wit_1 : add_factors_safety_wit_1.
Axiom proof_of_add_factors_safety_wit_2 : add_factors_safety_wit_2.
Axiom proof_of_add_factors_safety_wit_3 : add_factors_safety_wit_3.
Axiom proof_of_add_factors_safety_wit_4 : add_factors_safety_wit_4.
Axiom proof_of_add_factors_safety_wit_5 : add_factors_safety_wit_5.
Axiom proof_of_add_factors_safety_wit_6 : add_factors_safety_wit_6.
Axiom proof_of_add_factors_safety_wit_7 : add_factors_safety_wit_7.
Axiom proof_of_add_factors_safety_wit_8 : add_factors_safety_wit_8.
Axiom proof_of_add_factors_safety_wit_9 : add_factors_safety_wit_9.
Axiom proof_of_add_factors_safety_wit_10 : add_factors_safety_wit_10.
Axiom proof_of_add_factors_safety_wit_11 : add_factors_safety_wit_11.
Axiom proof_of_add_factors_safety_wit_12 : add_factors_safety_wit_12.
Axiom proof_of_add_factors_safety_wit_13 : add_factors_safety_wit_13.
Axiom proof_of_add_factors_safety_wit_14 : add_factors_safety_wit_14.
Axiom proof_of_add_factors_safety_wit_15 : add_factors_safety_wit_15.
Axiom proof_of_add_factors_safety_wit_16 : add_factors_safety_wit_16.
Axiom proof_of_add_factors_entail_wit_1 : add_factors_entail_wit_1.
Axiom proof_of_add_factors_entail_wit_2 : add_factors_entail_wit_2.
Axiom proof_of_add_factors_entail_wit_3_1 : add_factors_entail_wit_3_1.
Axiom proof_of_add_factors_entail_wit_3_2 : add_factors_entail_wit_3_2.
Axiom proof_of_add_factors_entail_wit_4 : add_factors_entail_wit_4.
Axiom proof_of_add_factors_entail_wit_5_1 : add_factors_entail_wit_5_1.
Axiom proof_of_add_factors_entail_wit_5_2 : add_factors_entail_wit_5_2.
Axiom proof_of_add_factors_return_wit_1 : add_factors_return_wit_1.
Axiom proof_of_add_factors_return_wit_2 : add_factors_return_wit_2.
Axiom proof_of_add_factors_partial_solve_wit_1_pure : add_factors_partial_solve_wit_1_pure.
Axiom proof_of_add_factors_partial_solve_wit_1 : add_factors_partial_solve_wit_1.
Axiom proof_of_add_factors_partial_solve_wit_2 : add_factors_partial_solve_wit_2.
Axiom proof_of_add_factors_partial_solve_wit_3 : add_factors_partial_solve_wit_3.
Axiom proof_of_add_factors_partial_solve_wit_4_pure : add_factors_partial_solve_wit_4_pure.
Axiom proof_of_add_factors_partial_solve_wit_4 : add_factors_partial_solve_wit_4.
Axiom proof_of_add_factors_partial_solve_wit_5_pure : add_factors_partial_solve_wit_5_pure.
Axiom proof_of_add_factors_partial_solve_wit_5 : add_factors_partial_solve_wit_5.
Axiom proof_of_add_factors_which_implies_wit_1 : add_factors_which_implies_wit_1.
Axiom proof_of_add_factors_which_implies_wit_2 : add_factors_which_implies_wit_2.
Axiom proof_of_cost_for_prime_safety_wit_1 : cost_for_prime_safety_wit_1.
Axiom proof_of_cost_for_prime_safety_wit_2 : cost_for_prime_safety_wit_2.
Axiom proof_of_cost_for_prime_safety_wit_3 : cost_for_prime_safety_wit_3.
Axiom proof_of_cost_for_prime_safety_wit_4 : cost_for_prime_safety_wit_4.
Axiom proof_of_cost_for_prime_safety_wit_5 : cost_for_prime_safety_wit_5.
Axiom proof_of_cost_for_prime_safety_wit_6 : cost_for_prime_safety_wit_6.
Axiom proof_of_cost_for_prime_safety_wit_7 : cost_for_prime_safety_wit_7.
Axiom proof_of_cost_for_prime_safety_wit_8 : cost_for_prime_safety_wit_8.
Axiom proof_of_cost_for_prime_safety_wit_9 : cost_for_prime_safety_wit_9.
Axiom proof_of_cost_for_prime_safety_wit_10 : cost_for_prime_safety_wit_10.
Axiom proof_of_cost_for_prime_safety_wit_11 : cost_for_prime_safety_wit_11.
Axiom proof_of_cost_for_prime_safety_wit_12 : cost_for_prime_safety_wit_12.
Axiom proof_of_cost_for_prime_safety_wit_13 : cost_for_prime_safety_wit_13.
Axiom proof_of_cost_for_prime_safety_wit_14 : cost_for_prime_safety_wit_14.
Axiom proof_of_cost_for_prime_safety_wit_15 : cost_for_prime_safety_wit_15.
Axiom proof_of_cost_for_prime_safety_wit_16 : cost_for_prime_safety_wit_16.
Axiom proof_of_cost_for_prime_safety_wit_17 : cost_for_prime_safety_wit_17.
Axiom proof_of_cost_for_prime_safety_wit_18 : cost_for_prime_safety_wit_18.
Axiom proof_of_cost_for_prime_safety_wit_19 : cost_for_prime_safety_wit_19.
Axiom proof_of_cost_for_prime_safety_wit_20 : cost_for_prime_safety_wit_20.
Axiom proof_of_cost_for_prime_safety_wit_21 : cost_for_prime_safety_wit_21.
Axiom proof_of_cost_for_prime_safety_wit_22 : cost_for_prime_safety_wit_22.
Axiom proof_of_cost_for_prime_safety_wit_23 : cost_for_prime_safety_wit_23.
Axiom proof_of_cost_for_prime_safety_wit_24 : cost_for_prime_safety_wit_24.
Axiom proof_of_cost_for_prime_safety_wit_25 : cost_for_prime_safety_wit_25.
Axiom proof_of_cost_for_prime_safety_wit_26 : cost_for_prime_safety_wit_26.
Axiom proof_of_cost_for_prime_safety_wit_27 : cost_for_prime_safety_wit_27.
Axiom proof_of_cost_for_prime_safety_wit_28 : cost_for_prime_safety_wit_28.
Axiom proof_of_cost_for_prime_safety_wit_29 : cost_for_prime_safety_wit_29.
Axiom proof_of_cost_for_prime_safety_wit_30 : cost_for_prime_safety_wit_30.
Axiom proof_of_cost_for_prime_safety_wit_31 : cost_for_prime_safety_wit_31.
Axiom proof_of_cost_for_prime_safety_wit_32 : cost_for_prime_safety_wit_32.
Axiom proof_of_cost_for_prime_safety_wit_33 : cost_for_prime_safety_wit_33.
Axiom proof_of_cost_for_prime_safety_wit_34 : cost_for_prime_safety_wit_34.
Axiom proof_of_cost_for_prime_safety_wit_35 : cost_for_prime_safety_wit_35.
Axiom proof_of_cost_for_prime_safety_wit_36 : cost_for_prime_safety_wit_36.
Axiom proof_of_cost_for_prime_safety_wit_37 : cost_for_prime_safety_wit_37.
Axiom proof_of_cost_for_prime_safety_wit_38 : cost_for_prime_safety_wit_38.
Axiom proof_of_cost_for_prime_safety_wit_39 : cost_for_prime_safety_wit_39.
Axiom proof_of_cost_for_prime_safety_wit_40 : cost_for_prime_safety_wit_40.
Axiom proof_of_cost_for_prime_safety_wit_41 : cost_for_prime_safety_wit_41.
Axiom proof_of_cost_for_prime_safety_wit_42 : cost_for_prime_safety_wit_42.
Axiom proof_of_cost_for_prime_safety_wit_43 : cost_for_prime_safety_wit_43.
Axiom proof_of_cost_for_prime_safety_wit_44 : cost_for_prime_safety_wit_44.
Axiom proof_of_cost_for_prime_safety_wit_45 : cost_for_prime_safety_wit_45.
Axiom proof_of_cost_for_prime_safety_wit_46 : cost_for_prime_safety_wit_46.
Axiom proof_of_cost_for_prime_safety_wit_47 : cost_for_prime_safety_wit_47.
Axiom proof_of_cost_for_prime_safety_wit_48 : cost_for_prime_safety_wit_48.
Axiom proof_of_cost_for_prime_safety_wit_49 : cost_for_prime_safety_wit_49.
Axiom proof_of_cost_for_prime_safety_wit_50 : cost_for_prime_safety_wit_50.
Axiom proof_of_cost_for_prime_safety_wit_51 : cost_for_prime_safety_wit_51.
Axiom proof_of_cost_for_prime_safety_wit_52 : cost_for_prime_safety_wit_52.
Axiom proof_of_cost_for_prime_safety_wit_53 : cost_for_prime_safety_wit_53.
Axiom proof_of_cost_for_prime_safety_wit_54 : cost_for_prime_safety_wit_54.
Axiom proof_of_cost_for_prime_safety_wit_55 : cost_for_prime_safety_wit_55.
Axiom proof_of_cost_for_prime_safety_wit_56 : cost_for_prime_safety_wit_56.
Axiom proof_of_cost_for_prime_safety_wit_57 : cost_for_prime_safety_wit_57.
Axiom proof_of_cost_for_prime_safety_wit_58 : cost_for_prime_safety_wit_58.
Axiom proof_of_cost_for_prime_safety_wit_59 : cost_for_prime_safety_wit_59.
Axiom proof_of_cost_for_prime_safety_wit_60 : cost_for_prime_safety_wit_60.
Axiom proof_of_cost_for_prime_safety_wit_61 : cost_for_prime_safety_wit_61.
Axiom proof_of_cost_for_prime_safety_wit_62 : cost_for_prime_safety_wit_62.
Axiom proof_of_cost_for_prime_safety_wit_63 : cost_for_prime_safety_wit_63.
Axiom proof_of_cost_for_prime_safety_wit_64 : cost_for_prime_safety_wit_64.
Axiom proof_of_cost_for_prime_entail_wit_1 : cost_for_prime_entail_wit_1.
Axiom proof_of_cost_for_prime_entail_wit_2_1 : cost_for_prime_entail_wit_2_1.
Axiom proof_of_cost_for_prime_entail_wit_2_2 : cost_for_prime_entail_wit_2_2.
Axiom proof_of_cost_for_prime_entail_wit_2_3 : cost_for_prime_entail_wit_2_3.
Axiom proof_of_cost_for_prime_entail_wit_2_4 : cost_for_prime_entail_wit_2_4.
Axiom proof_of_cost_for_prime_entail_wit_3 : cost_for_prime_entail_wit_3.
Axiom proof_of_cost_for_prime_entail_wit_4 : cost_for_prime_entail_wit_4.
Axiom proof_of_cost_for_prime_entail_wit_5_1 : cost_for_prime_entail_wit_5_1.
Axiom proof_of_cost_for_prime_entail_wit_5_2 : cost_for_prime_entail_wit_5_2.
Axiom proof_of_cost_for_prime_entail_wit_6 : cost_for_prime_entail_wit_6.
Axiom proof_of_cost_for_prime_entail_wit_7 : cost_for_prime_entail_wit_7.
Axiom proof_of_cost_for_prime_entail_wit_8 : cost_for_prime_entail_wit_8.
Axiom proof_of_cost_for_prime_entail_wit_9 : cost_for_prime_entail_wit_9.
Axiom proof_of_cost_for_prime_return_wit_1 : cost_for_prime_return_wit_1.
Axiom proof_of_cost_for_prime_return_wit_2 : cost_for_prime_return_wit_2.
Axiom proof_of_cost_for_prime_partial_solve_wit_1 : cost_for_prime_partial_solve_wit_1.
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
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.

End VC_Correct.
