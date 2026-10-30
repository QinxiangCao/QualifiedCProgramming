From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))),
  ((( &( "inside" ) )) # Int  |->_)
  **  ((( &( "runs" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))),
  ((( &( "runs" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "inside" ) )) # Int  |-> 0)
  **  ((( &( "runs" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= runs)) (PreH9 : (runs <= i)) (PreH10 : (0 <= inside)) (PreH11 : (inside <= 1)) (PreH12 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (inside = 0)) (PreH2 : ((Znth i input 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ ((runs + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (runs + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (inside = 0)) (PreH2 : ((Znth i input 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> (runs + 1 ))
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (inside = 0)) (PreH2 : ((Znth i input 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> (runs + 1 ))
  **  ((( &( "inside" ) )) # Int  |-> 1)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= runs)) (PreH10 : (runs <= i)) (PreH11 : (0 <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (inside <> 0)) (PreH2 : ((Znth i input 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) = 0)) (PreH2 : (inside = 0)) (PreH3 : ((Znth i input 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= runs)) (PreH12 : (runs <= i)) (PreH13 : (0 <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> (runs + 1 ))
  **  ((( &( "inside" ) )) # Int  |-> 1)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ False ”
.

Definition solver_safety_wit_11 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) <> 0)) (PreH2 : ((Znth i input 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ False ”
.

Definition solver_safety_wit_12 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) = 0)) (PreH2 : (inside <> 0)) (PreH3 : ((Znth i input 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= runs)) (PreH12 : (runs <= i)) (PreH13 : (0 <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ False ”
.

Definition solver_safety_wit_13 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) = 0)) (PreH2 : ((Znth i input 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) = 0)) (PreH2 : ((Znth i input 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> 0)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) <> 0)) (PreH2 : (inside = 0)) (PreH3 : ((Znth i input 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= runs)) (PreH12 : (runs <= i)) (PreH13 : (0 <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> (runs + 1 ))
  **  ((( &( "inside" ) )) # Int  |-> 1)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) <> 0)) (PreH2 : (inside <> 0)) (PreH3 : ((Znth i input 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= runs)) (PreH12 : (runs <= i)) (PreH13 : (0 <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_17 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= runs)) (PreH9 : (runs <= i)) (PreH10 : (0 <= inside)) (PreH11 : (inside <= 1)) (PreH12 : (ScanState input i runs inside )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_18 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (runs > 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= runs)) (PreH10 : (runs <= i)) (PreH11 : (0 <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "runs" ) )) # Int  |-> runs)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_entail_wit_1 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (1 <= (Zlength (input))) ”
  &&  “ ((Zlength (input)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ (ScanState input 0 0 0 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))),
  TT && emp 
|--
  “ (ScanState input 0 0 0 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))),
  (ScanState input 0 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (input: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))
.

Definition solver_entail_wit_2_1 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) = 0)) (PreH2 : ((Znth i input 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (1 <= (Zlength (input))) ”
  &&  “ ((Zlength (input)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= runs) ”
  &&  “ (runs <= (i + 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ (ScanState input (i + 1 ) runs 0 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) = 0)) (PreH2 : ((Znth i input 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  TT && emp 
|--
  “ (ScanState input (i + 1 ) runs 0 ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) = 0)) (PreH2 : ((Znth i input 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (ScanState input (i + 1 ) runs 0 )
.

Definition solver_entail_wit_2_2 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) <> 0)) (PreH2 : (inside = 0)) (PreH3 : ((Znth i input 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= runs)) (PreH12 : (runs <= i)) (PreH13 : (0 <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (1 <= (Zlength (input))) ”
  &&  “ ((Zlength (input)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (runs + 1 )) ”
  &&  “ ((runs + 1 ) <= (i + 1 )) ”
  &&  “ (0 <= 1) ”
  &&  “ (1 <= 1) ”
  &&  “ (ScanState input (i + 1 ) (runs + 1 ) 1 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) <> 0)) (PreH2 : (inside = 0)) (PreH3 : ((Znth i input 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= runs)) (PreH12 : (runs <= i)) (PreH13 : (0 <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside )),
  TT && emp 
|--
  “ (ScanState input (i + 1 ) (runs + 1 ) 1 ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) <> 0)) (PreH2 : (inside = 0)) (PreH3 : ((Znth i input 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= runs)) (PreH12 : (runs <= i)) (PreH13 : (0 <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside )),
  (ScanState input (i + 1 ) (runs + 1 ) 1 )
.

Definition solver_entail_wit_2_3 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) <> 0)) (PreH2 : (inside <> 0)) (PreH3 : ((Znth i input 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= runs)) (PreH12 : (runs <= i)) (PreH13 : (0 <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (1 <= (Zlength (input))) ”
  &&  “ ((Zlength (input)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= runs) ”
  &&  “ (runs <= (i + 1 )) ”
  &&  “ (0 <= inside) ”
  &&  “ (inside <= 1) ”
  &&  “ (ScanState input (i + 1 ) runs inside ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) <> 0)) (PreH2 : (inside <> 0)) (PreH3 : ((Znth i input 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= runs)) (PreH12 : (runs <= i)) (PreH13 : (0 <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside )),
  TT && emp 
|--
  “ (ScanState input (i + 1 ) runs inside ) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) <> 0)) (PreH2 : (inside <> 0)) (PreH3 : ((Znth i input 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= runs)) (PreH12 : (runs <= i)) (PreH13 : (0 <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside )),
  (ScanState input (i + 1 ) runs inside )
.

Definition solver_return_wit_1 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (runs > 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= runs)) (PreH10 : (runs <= i)) (PreH11 : (0 <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (Spec input 2 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (runs > 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= runs)) (PreH10 : (runs <= i)) (PreH11 : (0 <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside )),
  TT && emp 
|--
  “ (Spec input 2 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (runs > 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= runs)) (PreH10 : (runs <= i)) (PreH11 : (0 <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside )),
  (Spec input 2 )
.

Definition solver_return_wit_2 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (runs <= 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= runs)) (PreH10 : (runs <= i)) (PreH11 : (0 <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (Spec input runs ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (runs <= 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= runs)) (PreH10 : (runs <= i)) (PreH11 : (0 <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside )),
  TT && emp 
|--
  “ (Spec input runs ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (runs <= 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= runs)) (PreH10 : (runs <= i)) (PreH11 : (0 <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside )),
  (Spec input runs )
.

Definition solver_partial_solve_wit_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= runs)) (PreH9 : (runs <= i)) (PreH10 : (0 <= inside)) (PreH11 : (inside <= 1)) (PreH12 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input))) ”
  &&  “ (1 <= (Zlength (input))) ”
  &&  “ ((Zlength (input)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= runs) ”
  &&  “ (runs <= i) ”
  &&  “ (0 <= inside) ”
  &&  “ (inside <= 1) ”
  &&  “ (ScanState input i runs inside ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
.

Definition solver_partial_solve_wit_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (inside = 0)) (PreH2 : ((Znth i input 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (inside = 0) ”
  &&  “ ((Znth i input 0) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input))) ”
  &&  “ (1 <= (Zlength (input))) ”
  &&  “ ((Zlength (input)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= runs) ”
  &&  “ (runs <= i) ”
  &&  “ (0 <= inside) ”
  &&  “ (inside <= 1) ”
  &&  “ (ScanState input i runs inside ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
.

Definition solver_partial_solve_wit_3 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : ((Znth i input 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= runs)) (PreH10 : (runs <= i)) (PreH11 : (0 <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ ((Znth i input 0) = 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input))) ”
  &&  “ (1 <= (Zlength (input))) ”
  &&  “ ((Zlength (input)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= runs) ”
  &&  “ (runs <= i) ”
  &&  “ (0 <= inside) ”
  &&  “ (inside <= 1) ”
  &&  “ (ScanState input i runs inside ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
.

Definition solver_partial_solve_wit_4 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (inside: Z) (runs: Z) (i: Z) (PreH1 : (inside <> 0)) (PreH2 : ((Znth i input 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= runs)) (PreH11 : (runs <= i)) (PreH12 : (0 <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
|--
  “ (inside <> 0) ”
  &&  “ ((Znth i input 0) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input))) ”
  &&  “ (1 <= (Zlength (input))) ”
  &&  “ ((Zlength (input)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input)))) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= runs) ”
  &&  “ (runs <= i) ”
  &&  “ (0 <= inside) ”
  &&  “ (inside <= 1) ”
  &&  “ (ScanState input i runs inside ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 200005 )
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
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.

End VC_Correct.
