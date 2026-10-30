From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib.
Local Open Scope sac.

(*----- Function cmp_int -----*)

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))),
  ((( &( "pc" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "primes" ) ) 4000 )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full values_pre n_pre a )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))),
  ((( &( "i" ) )) # Int  |->_)
  **  (UCharArray.full ( &( "composite" ) ) 31624 (repeat_Z (0) (31624)) )
  **  ((( &( "pc" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "primes" ) ) 4000 )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full values_pre n_pre a )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_3 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH5 : (2 <= i)) (PreH6 : (i <= 31624)) (PreH7 : (pc = (Zlength (prime_data)))) (PreH8 : (0 <= pc)) (PreH9 : (pc < 4000)) (PreH10 : ((Zlength (composite_data)) = 31624)) (PreH11 : (PrimePrefixTable2 i prime_data composite_data )),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (31623 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 31623) ”
.

Definition solver_safety_wit_4 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((Znth i composite_data 0) = 0)) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data )),
  (IntArray.full ( &( "primes" ) ) (pc + 1 ) (app (prime_data) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "primes" ) ) (pc + 1 ) 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  (IntArray.full values_pre n_pre a )
|--
  “ ((pc + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (pc + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((Znth i composite_data 0) = 0)) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data )),
  (IntArray.full ( &( "primes" ) ) (pc + 1 ) (app (prime_data) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "primes" ) ) (pc + 1 ) 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> (pc + 1 ))
  **  (IntArray.full values_pre n_pre a )
|--
  “ ((i * i ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (i * i )) ”
.

Definition solver_safety_wit_6 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((Znth i composite_data 0) = 0)) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data )),
  (IntArray.full ( &( "primes" ) ) (pc + 1 ) (app (prime_data) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "primes" ) ) (pc + 1 ) 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> (pc + 1 ))
  **  (IntArray.full values_pre n_pre a )
|--
  “ (31623 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 31623) ”
.

Definition solver_safety_wit_7 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) <= 31623)) (PreH2 : ((Znth i composite_data 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data composite_data )),
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full ( &( "primes" ) ) (pc + 1 ) (app (prime_data) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "primes" ) ) (pc + 1 ) 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> (pc + 1 ))
  **  (IntArray.full values_pre n_pre a )
|--
  “ ((i * i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i * i )) ”
.

Definition solver_safety_wit_8 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (j: Z) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH5 : (2 <= i)) (PreH6 : (i <= 177)) (PreH7 : (pc = (Zlength (prime_data)))) (PreH8 : (1 <= pc)) (PreH9 : (pc < 4000)) (PreH10 : ((i * i ) <= j)) (PreH11 : (j <= (31623 + i ))) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimeMarkTable2 i j prime_data composite_data )),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (31623 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 31623) ”
.

Definition solver_safety_wit_9 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (j: Z) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data composite_data )),
  (UCharArray.full ( &( "composite" ) ) 31624 (replace_Znth (j) (1) (composite_data)) )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
|--
  “ ((j + i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + i )) ”
.

Definition solver_safety_wit_10 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (j: Z) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data composite_data )),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 31624)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (PrimePrefixTable2 i prime_data composite_data )),
  ((( &( "factors" ) )) # Ptr  |->_)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ ((n_pre * 10 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre * 10 )) ”
.

Definition solver_safety_wit_12 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 31624)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (PrimePrefixTable2 i prime_data composite_data )),
  ((( &( "factors" ) )) # Ptr  |->_)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition solver_safety_wit_13 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (j: Z) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data composite_data )),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) > 31623)) (PreH2 : ((Znth i composite_data 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data composite_data )),
  (IntArray.full ( &( "primes" ) ) (pc + 1 ) (app (prime_data) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "primes" ) ) (pc + 1 ) 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> (pc + 1 ))
  **  (IntArray.full values_pre n_pre a )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((Znth i composite_data 0) <> 0)) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data )),
  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data )),
  ((( &( "count" ) )) # Int  |->_)
  **  (IntArray.undef_full retval (n_pre * 10 ) )
  **  ((( &( "factors" ) )) # Ptr  |-> retval)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval (n_pre * 10 ) )
  **  ((( &( "factors" ) )) # Ptr  |-> retval)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (count = (Zlength (factor_data)))) (PreH13 : (0 <= count)) (PreH14 : (count <= (i * 10 ))) (PreH15 : (CompletePrimeTable prime_data )) (PreH16 : (PrimeFactorBagPrefix a i factor_data )),
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full values_pre n_pre a )
  **  ((( &( "x" ) )) # Int  |-> (Znth i a 0))
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (0 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorScanState a prime_data i j x factor_data )) (PreH21 : (FactorScanState2 a prime_data i j x factor_data )) (PreH22 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth j prime_data 0) * (Znth j prime_data 0) )) ”
) \/
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (0 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorScanState a prime_data i j x factor_data )) (PreH21 : (FactorScanState2 a prime_data i j x factor_data )) (PreH22 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth j prime_data 0) * (Znth j prime_data 0) )) ”
).

Definition solver_safety_wit_19_split_goal_1 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (0 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorScanState a prime_data i j x factor_data )) (PreH21 : (FactorScanState2 a prime_data i j x factor_data )) (PreH22 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (0 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorScanState a prime_data i j x factor_data )) (PreH21 : (FactorScanState2 a prime_data i j x factor_data )) (PreH22 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((INT64_MIN) <= ((Znth j prime_data 0) * (Znth j prime_data 0) )) ”
.

Definition solver_safety_wit_20 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x <> (INT_MIN)) \/ ((Znth j prime_data 0) <> (-1))) ”
  &&  “ ((Znth j prime_data 0) <> 0) ”
) \/
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x <> (INT_MIN)) \/ ((Znth j prime_data 0) <> (-1))) ”
  &&  “ ((Znth j prime_data 0) <> 0) ”
).

Definition solver_safety_wit_20_split_goal_1 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x <> (INT_MIN)) \/ ((Znth j prime_data 0) <> (-1))) ”
.

Definition solver_safety_wit_20_split_goal_2 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((Znth j prime_data 0) <> 0) ”
.

Definition solver_safety_wit_21 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_22 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data 0) ) ) = 0)) (PreH2 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data )) (PreH22 : (FactorScanState a prime_data i j x factor_data )) (PreH23 : (FactorScanState2 a prime_data i j x factor_data )) (PreH24 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full factors (count + 1 ) (app (factor_data) ((cons ((Znth j prime_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_23 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10 ) + 9 ))) (PreH18 : (CompletePrimeTable prime_data )) (PreH19 : (FactorDivideState a prime_data i j x factor_data )) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x <> (INT_MIN)) \/ ((Znth j prime_data 0) <> (-1))) ”
  &&  “ ((Znth j prime_data 0) <> 0) ”
) \/
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10 ) + 9 ))) (PreH18 : (CompletePrimeTable prime_data )) (PreH19 : (FactorDivideState a prime_data i j x factor_data )) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x <> (INT_MIN)) \/ ((Znth j prime_data 0) <> (-1))) ”
  &&  “ ((Znth j prime_data 0) <> 0) ”
).

Definition solver_safety_wit_23_split_goal_1 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10 ) + 9 ))) (PreH18 : (CompletePrimeTable prime_data )) (PreH19 : (FactorDivideState a prime_data i j x factor_data )) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x <> (INT_MIN)) \/ ((Znth j prime_data 0) <> (-1))) ”
.

Definition solver_safety_wit_23_split_goal_2 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10 ) + 9 ))) (PreH18 : (CompletePrimeTable prime_data )) (PreH19 : (FactorDivideState a prime_data i j x factor_data )) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((Znth j prime_data 0) <> 0) ”
.

Definition solver_safety_wit_24 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10 ) + 9 ))) (PreH18 : (CompletePrimeTable prime_data )) (PreH19 : (FactorDivideState a prime_data i j x factor_data )) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_25 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorDivideState a prime_data i j x factor_data )) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x <> (INT_MIN)) \/ ((Znth j prime_data 0) <> (-1))) ”
  &&  “ ((Znth j prime_data 0) <> 0) ”
) \/
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorDivideState a prime_data i j x factor_data )) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x <> (INT_MIN)) \/ ((Znth j prime_data 0) <> (-1))) ”
  &&  “ ((Znth j prime_data 0) <> 0) ”
).

Definition solver_safety_wit_25_split_goal_1 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorDivideState a prime_data i j x factor_data )) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x <> (INT_MIN)) \/ ((Znth j prime_data 0) <> (-1))) ”
.

Definition solver_safety_wit_25_split_goal_2 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorDivideState a prime_data i j x factor_data )) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((Znth j prime_data 0) <> 0) ”
.

Definition solver_safety_wit_26 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data 0) ) ) <> 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorDivideState a prime_data i j x factor_data )) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_27 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data 0) ) ) <> 0)) (PreH2 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data )) (PreH22 : (FactorScanState a prime_data i j x factor_data )) (PreH23 : (FactorScanState2 a prime_data i j x factor_data )) (PreH24 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_28 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (j >= pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (0 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorScanState a prime_data i j x factor_data )) (PreH21 : (FactorScanState2 a prime_data i j x factor_data )) (PreH22 : (FactorAppendCapacity prime_data i j x count )),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_29 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) > x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_30 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full factors (count + 1 ) (app (factor_data) ((cons (x) ((@nil Z))))) )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_31 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data )) (PreH22 : (FactorScanState a prime_data i j x factor_data )) (PreH23 : (FactorScanState2 a prime_data i j x factor_data )) (PreH24 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full factors (count + 1 ) (app (factor_data) ((cons (x) ((@nil Z))))) )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_32 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full factors (count + 1 ) (app (factor_data) ((cons (x) ((@nil Z))))) )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_33 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data )) (PreH22 : (FactorScanState a prime_data i j x factor_data )) (PreH23 : (FactorScanState2 a prime_data i j x factor_data )) (PreH24 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full factors (count + 1 ) (app (factor_data) ((cons (x) ((@nil Z))))) )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_34 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_35 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data )) (PreH22 : (FactorScanState a prime_data i j x factor_data )) (PreH23 : (FactorScanState2 a prime_data i j x factor_data )) (PreH24 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_36 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (Permutation factor_data sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * 10 ))) (PreH18 : (CompletePrimeTable prime_data )) (PreH19 : (PrimeFactorBagPrefix a i factor_data )),
  ((( &( "ok" ) )) # Int  |->_)
  **  (IntArray.full factors count sorted )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_37 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (Permutation factor_data sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * 10 ))) (PreH18 : (CompletePrimeTable prime_data )) (PreH19 : (PrimeFactorBagPrefix a i factor_data )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  (IntArray.full factors count sorted )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_38 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (ok: Z) (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : (i < count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : (0 <= count)) (PreH6 : (count <= (n_pre * 10 ))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1 ))) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : ((Zlength (sorted)) = count)) (PreH14 : (increasing sorted )) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH16 : (DuplicateScanLoopState sorted count i ok )),
  (IntArray.full factors count sorted )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_39 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (ok: Z) (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : (i < count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : (0 <= count)) (PreH6 : (count <= (n_pre * 10 ))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1 ))) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : ((Zlength (sorted)) = count)) (PreH14 : (increasing sorted )) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH16 : (DuplicateScanLoopState sorted count i ok )),
  (IntArray.full factors count sorted )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_40 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (ok: Z) (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : ((Znth i sorted 0) = (Znth (i - 1 ) sorted 0))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n_pre * 10 ))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1 ))) (PreH10 : (pc = (Zlength (prime_data)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : ((Zlength (sorted)) = count)) (PreH15 : (increasing sorted )) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH17 : (DuplicateScanLoopState sorted count i ok )),
  (IntArray.full factors count sorted )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_41 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (ok: Z) (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : ((Znth i sorted 0) = (Znth (i - 1 ) sorted 0))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n_pre * 10 ))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1 ))) (PreH10 : (pc = (Zlength (prime_data)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : ((Zlength (sorted)) = count)) (PreH15 : (increasing sorted )) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH17 : (DuplicateScanLoopState sorted count i ok )),
  (IntArray.full factors count sorted )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "ok" ) )) # Int  |-> 1)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_42 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (ok: Z) (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : ((Znth i sorted 0) <> (Znth (i - 1 ) sorted 0))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n_pre * 10 ))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1 ))) (PreH10 : (pc = (Zlength (prime_data)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : ((Zlength (sorted)) = count)) (PreH15 : (increasing sorted )) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH17 : (DuplicateScanLoopState sorted count i ok )),
  (IntArray.full factors count sorted )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))),
  (UCharArray.full ( &( "composite" ) ) 31624 (repeat_Z (0) (31624)) )
  **  (IntArray.undef_full ( &( "primes" ) ) 4000 )
  **  (IntArray.full values_pre n_pre a )
|--
  EX (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= 31624) ”
  &&  “ (0 = (Zlength (prime_data))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (PrimePrefixTable2 2 prime_data composite_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) 0 prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) 0 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))),
  TT && emp 
|--
  “ (PrimePrefixTable2 2 (@nil Z) (repeat_Z (0) (31624)) ) ”
  &&  “ ((Zlength ((repeat_Z (0) (31624)))) = 31624) ”
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))),
  (PrimePrefixTable2 2 (@nil Z) (repeat_Z (0) (31624)) )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))),
  ((Zlength ((repeat_Z (0) (31624)))) = 31624)
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))),
  (0 = (Zlength ((@nil Z))))
.

Definition solver_entail_wit_1_split_goal_4 :=
forall (a: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (a)))) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_2 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) <= 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  (IntArray.full ( &( "primes" ) ) (pc + 1 ) (app (prime_data_2) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "primes" ) ) (pc + 1 ) 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.full values_pre n_pre a )
|--
  EX (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (2 <= i) ”
  &&  “ (i <= 177) ”
  &&  “ ((pc + 1 ) = (Zlength (prime_data))) ”
  &&  “ (1 <= (pc + 1 )) ”
  &&  “ ((pc + 1 ) < 4000) ”
  &&  “ ((i * i ) <= (i * i )) ”
  &&  “ ((i * i ) <= (31623 + i )) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (PrimeMarkTable2 i (i * i ) prime_data composite_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) (pc + 1 ) prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) (pc + 1 ) 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) <= 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  TT && emp 
|--
  “ (PrimeMarkTable2 i (i * i ) (app (prime_data_2) ((cons (i) ((@nil Z))))) composite_data_2 ) ”
  &&  “ ((pc + 1 ) < 4000) ”
  &&  “ ((pc + 1 ) = (Zlength ((app (prime_data_2) ((cons (i) ((@nil Z)))))))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) <= 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  (PrimeMarkTable2 i (i * i ) (app (prime_data_2) ((cons (i) ((@nil Z))))) composite_data_2 )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) <= 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  ((pc + 1 ) < 4000)
.

Definition solver_entail_wit_2_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) <= 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  ((pc + 1 ) = (Zlength ((app (prime_data_2) ((cons (i) ((@nil Z))))))))
.

Definition solver_entail_wit_2_split_goal_4 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) <= 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_3 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data_2: (@list Z)) (j: Z) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2 )),
  (UCharArray.full ( &( "composite" ) ) 31624 (replace_Znth (j) (1) (composite_data_2)) )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
|--
  EX (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (2 <= i) ”
  &&  “ (i <= 177) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (1 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((i * i ) <= (j + i )) ”
  &&  “ ((j + i ) <= (31623 + i )) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (PrimeMarkTable2 i (j + i ) prime_data composite_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (j: Z) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2 )),
  TT && emp 
|--
  “ (PrimeMarkTable2 i (j + i ) prime_data_2 (replace_Znth (j) (1) (composite_data_2)) ) ”
  &&  “ ((Zlength ((replace_Znth (j) (1) (composite_data_2)))) = 31624) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (j: Z) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2 )),
  (PrimeMarkTable2 i (j + i ) prime_data_2 (replace_Znth (j) (1) (composite_data_2)) )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (j: Z) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2 )),
  ((Zlength ((replace_Znth (j) (1) (composite_data_2)))) = 31624)
.

Definition solver_entail_wit_4_1 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data_2: (@list Z)) (j: Z) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2 )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
|--
  EX (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (2 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= 31624) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (PrimePrefixTable2 (i + 1 ) prime_data composite_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (j: Z) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2 )),
  TT && emp 
|--
  “ (PrimePrefixTable2 (i + 1 ) prime_data_2 composite_data_2 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (j: Z) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2 )),
  (PrimePrefixTable2 (i + 1 ) prime_data_2 composite_data_2 )
.

Definition solver_entail_wit_4_1_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (j: Z) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2 )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_4_2 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) > 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  (IntArray.full ( &( "primes" ) ) (pc + 1 ) (app (prime_data_2) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "primes" ) ) (pc + 1 ) 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.full values_pre n_pre a )
|--
  EX (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (2 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= 31624) ”
  &&  “ ((pc + 1 ) = (Zlength (prime_data))) ”
  &&  “ (0 <= (pc + 1 )) ”
  &&  “ ((pc + 1 ) < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (PrimePrefixTable2 (i + 1 ) prime_data composite_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) (pc + 1 ) prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) (pc + 1 ) 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) > 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  TT && emp 
|--
  “ (PrimePrefixTable2 (i + 1 ) (app (prime_data_2) ((cons (i) ((@nil Z))))) composite_data_2 ) ”
  &&  “ ((pc + 1 ) < 4000) ”
  &&  “ ((pc + 1 ) = (Zlength ((app (prime_data_2) ((cons (i) ((@nil Z)))))))) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) > 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  (PrimePrefixTable2 (i + 1 ) (app (prime_data_2) ((cons (i) ((@nil Z))))) composite_data_2 )
.

Definition solver_entail_wit_4_2_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) > 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  ((pc + 1 ) < 4000)
.

Definition solver_entail_wit_4_2_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((i * i ) > 31623)) (PreH2 : ((Znth i composite_data_2 0) = 0)) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  ((pc + 1 ) = (Zlength ((app (prime_data_2) ((cons (i) ((@nil Z))))))))
.

Definition solver_entail_wit_4_3 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((Znth i composite_data_2 0) <> 0)) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
|--
  EX (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (2 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= 31624) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (PrimePrefixTable2 (i + 1 ) prime_data composite_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((Znth i composite_data_2 0) <> 0)) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  TT && emp 
|--
  “ (PrimePrefixTable2 (i + 1 ) prime_data_2 composite_data_2 ) ”
  &&  emp
).

Definition solver_entail_wit_4_3_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((Znth i composite_data_2 0) <> 0)) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  (PrimePrefixTable2 (i + 1 ) prime_data_2 composite_data_2 )
.

Definition solver_entail_wit_5 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  (IntArray.undef_full retval (n_pre * 10 ) )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
|--
  EX (factor_data: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (0 = (Zlength (factor_data))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (0 * 10 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (PrimeFactorBagPrefix a 0 factor_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full retval 0 factor_data )
  **  (IntArray.undef_seg retval 0 (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  TT && emp 
|--
  “ (PrimeFactorBagPrefix a 0 (@nil Z) ) ”
  &&  “ (CompletePrimeTable prime_data_2 ) ”
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  (PrimeFactorBagPrefix a 0 (@nil Z) )
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  (CompletePrimeTable prime_data_2 )
.

Definition solver_entail_wit_5_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  (0 = (Zlength ((@nil Z))))
.

Definition solver_entail_wit_5_split_goal_4 :=
forall (a: (@list Z)) (n_pre: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2 )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_6 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : (0 <= count)) (PreH14 : (count <= (i * 10 ))) (PreH15 : (CompletePrimeTable prime_data_2 )) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2 )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.full factors count factor_data_2 )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  EX (factor_data: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= pc) ”
  &&  “ (1 <= (Znth i a 0)) ”
  &&  “ ((Znth i a 0) <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorScanState a prime_data i 0 (Znth i a 0) factor_data ) ”
  &&  “ (FactorScanState2 a prime_data i 0 (Znth i a 0) factor_data ) ”
  &&  “ (FactorAppendCapacity prime_data i 0 (Znth i a 0) count ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : (0 <= count)) (PreH14 : (count <= (i * 10 ))) (PreH15 : (CompletePrimeTable prime_data_2 )) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2 )),
  TT && emp 
|--
  “ (FactorAppendCapacity prime_data_2 i 0 (Znth i a 0) count ) ”
  &&  “ (FactorScanState2 a prime_data_2 i 0 (Znth i a 0) factor_data_2 ) ”
  &&  “ (FactorScanState a prime_data_2 i 0 (Znth i a 0) factor_data_2 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : (0 <= count)) (PreH14 : (count <= (i * 10 ))) (PreH15 : (CompletePrimeTable prime_data_2 )) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2 )),
  (FactorAppendCapacity prime_data_2 i 0 (Znth i a 0) count )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : (0 <= count)) (PreH14 : (count <= (i * 10 ))) (PreH15 : (CompletePrimeTable prime_data_2 )) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2 )),
  (FactorScanState2 a prime_data_2 i 0 (Znth i a 0) factor_data_2 )
.

Definition solver_entail_wit_6_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : (0 <= count)) (PreH14 : (count <= (i * 10 ))) (PreH15 : (CompletePrimeTable prime_data_2 )) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2 )),
  (FactorScanState a prime_data_2 i 0 (Znth i a 0) factor_data_2 )
.

Definition solver_entail_wit_6_split_goal_4 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : (0 <= count)) (PreH14 : (count <= (i * 10 ))) (PreH15 : (CompletePrimeTable prime_data_2 )) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2 )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_7 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (IntArray.full factors (count + 1 ) (app (factor_data_2) ((cons ((Znth j prime_data_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
|--
  EX (factor_data: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ ((count + 1 ) = (Zlength (factor_data))) ”
  &&  “ (1 <= (count + 1 )) ”
  &&  “ ((count + 1 ) <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorDivideState a prime_data i j x factor_data ) ”
  &&  “ (FactorDivideState2 a prime_data i j x factor_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors (count + 1 ) factor_data )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  TT && emp 
|--
  “ (FactorDivideState2 a prime_data_2 i j x (app (factor_data_2) ((cons ((Znth j prime_data_2 0)) ((@nil Z))))) ) ”
  &&  “ (FactorDivideState a prime_data_2 i j x (app (factor_data_2) ((cons ((Znth j prime_data_2 0)) ((@nil Z))))) ) ”
  &&  “ ((count + 1 ) <= ((i * 10 ) + 9 )) ”
  &&  “ ((count + 1 ) = (Zlength ((app (factor_data_2) ((cons ((Znth j prime_data_2 0)) ((@nil Z)))))))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (FactorDivideState2 a prime_data_2 i j x (app (factor_data_2) ((cons ((Znth j prime_data_2 0)) ((@nil Z))))) )
.

Definition solver_entail_wit_7_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (FactorDivideState a prime_data_2 i j x (app (factor_data_2) ((cons ((Znth j prime_data_2 0)) ((@nil Z))))) )
.

Definition solver_entail_wit_7_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  ((count + 1 ) <= ((i * 10 ) + 9 ))
.

Definition solver_entail_wit_7_split_goal_4 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  ((count + 1 ) = (Zlength ((app (factor_data_2) ((cons ((Znth j prime_data_2 0)) ((@nil Z))))))))
.

Definition solver_entail_wit_7_split_goal_5 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_8 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.full factors count factor_data_2 )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  EX (factor_data: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < pc) ”
  &&  “ (1 <= (x ÷ (Znth j prime_data_2 0) )) ”
  &&  “ ((x ÷ (Znth j prime_data_2 0) ) <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorDivideState a prime_data i j (x ÷ (Znth j prime_data_2 0) ) factor_data ) ”
  &&  “ (FactorDivideState2 a prime_data i j (x ÷ (Znth j prime_data_2 0) ) factor_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  TT && emp 
|--
  “ (FactorDivideState2 a prime_data_2 i j (x ÷ (Znth j prime_data_2 0) ) factor_data_2 ) ”
  &&  “ (FactorDivideState a prime_data_2 i j (x ÷ (Znth j prime_data_2 0) ) factor_data_2 ) ”
  &&  “ ((x ÷ (Znth j prime_data_2 0) ) <= 1000000000) ”
  &&  “ (1 <= (x ÷ (Znth j prime_data_2 0) )) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  (FactorDivideState2 a prime_data_2 i j (x ÷ (Znth j prime_data_2 0) ) factor_data_2 )
.

Definition solver_entail_wit_8_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  (FactorDivideState a prime_data_2 i j (x ÷ (Znth j prime_data_2 0) ) factor_data_2 )
.

Definition solver_entail_wit_8_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  ((x ÷ (Znth j prime_data_2 0) ) <= 1000000000)
.

Definition solver_entail_wit_8_split_goal_4 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  (1 <= (x ÷ (Znth j prime_data_2 0) ))
.

Definition solver_entail_wit_9_1 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.full factors count factor_data_2 )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  EX (factor_data: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorScanState a prime_data i (j + 1 ) x factor_data ) ”
  &&  “ (FactorScanState2 a prime_data i (j + 1 ) x factor_data ) ”
  &&  “ (FactorAppendCapacity prime_data i (j + 1 ) x count ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  TT && emp 
|--
  “ (FactorAppendCapacity prime_data_2 i (j + 1 ) x count ) ”
  &&  “ (FactorScanState2 a prime_data_2 i (j + 1 ) x factor_data_2 ) ”
  &&  “ (FactorScanState a prime_data_2 i (j + 1 ) x factor_data_2 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_9_1_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  (FactorAppendCapacity prime_data_2 i (j + 1 ) x count )
.

Definition solver_entail_wit_9_1_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  (FactorScanState2 a prime_data_2 i (j + 1 ) x factor_data_2 )
.

Definition solver_entail_wit_9_1_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  (FactorScanState a prime_data_2 i (j + 1 ) x factor_data_2 )
.

Definition solver_entail_wit_9_1_split_goal_4 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data_2 )) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2 )) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2 )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_9_2 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.full factors count factor_data_2 )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  EX (factor_data: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorScanState a prime_data i (j + 1 ) x factor_data ) ”
  &&  “ (FactorScanState2 a prime_data i (j + 1 ) x factor_data ) ”
  &&  “ (FactorAppendCapacity prime_data i (j + 1 ) x count ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  TT && emp 
|--
  “ (FactorAppendCapacity prime_data_2 i (j + 1 ) x count ) ”
  &&  “ (FactorScanState2 a prime_data_2 i (j + 1 ) x factor_data_2 ) ”
  &&  “ (FactorScanState a prime_data_2 i (j + 1 ) x factor_data_2 ) ”
  &&  emp
).

Definition solver_entail_wit_9_2_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (FactorAppendCapacity prime_data_2 i (j + 1 ) x count )
.

Definition solver_entail_wit_9_2_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (FactorScanState2 a prime_data_2 i (j + 1 ) x factor_data_2 )
.

Definition solver_entail_wit_9_2_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data_2 0) ) ) <> 0)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (FactorScanState a prime_data_2 i (j + 1 ) x factor_data_2 )
.

Definition solver_entail_wit_10_1 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data_2 )) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count )),
  (IntArray.full factors (count + 1 ) (app (factor_data_2) ((cons (x) ((@nil Z))))) )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
|--
  EX (factor_data: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ ((count + 1 ) = (Zlength (factor_data))) ”
  &&  “ (0 <= (count + 1 )) ”
  &&  “ ((count + 1 ) <= ((i + 1 ) * 10 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (PrimeFactorBagPrefix a (i + 1 ) factor_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors (count + 1 ) factor_data )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data_2 )) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count )),
  TT && emp 
|--
  “ (PrimeFactorBagPrefix a (i + 1 ) (app (factor_data_2) ((cons (x) ((@nil Z))))) ) ”
  &&  “ ((count + 1 ) = (Zlength ((app (factor_data_2) ((cons (x) ((@nil Z)))))))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_10_1_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data_2 )) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count )),
  (PrimeFactorBagPrefix a (i + 1 ) (app (factor_data_2) ((cons (x) ((@nil Z))))) )
.

Definition solver_entail_wit_10_1_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data_2 )) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count )),
  ((count + 1 ) = (Zlength ((app (factor_data_2) ((cons (x) ((@nil Z))))))))
.

Definition solver_entail_wit_10_1_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data_2 )) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_10_2 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (IntArray.full factors (count + 1 ) (app (factor_data_2) ((cons (x) ((@nil Z))))) )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
|--
  EX (factor_data: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ ((count + 1 ) = (Zlength (factor_data))) ”
  &&  “ (0 <= (count + 1 )) ”
  &&  “ ((count + 1 ) <= ((i + 1 ) * 10 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (PrimeFactorBagPrefix a (i + 1 ) factor_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors (count + 1 ) factor_data )
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  TT && emp 
|--
  “ (PrimeFactorBagPrefix a (i + 1 ) (app (factor_data_2) ((cons (x) ((@nil Z))))) ) ”
  &&  “ ((count + 1 ) = (Zlength ((app (factor_data_2) ((cons (x) ((@nil Z)))))))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_10_2_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (PrimeFactorBagPrefix a (i + 1 ) (app (factor_data_2) ((cons (x) ((@nil Z))))) )
.

Definition solver_entail_wit_10_2_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  ((count + 1 ) = (Zlength ((app (factor_data_2) ((cons (x) ((@nil Z))))))))
.

Definition solver_entail_wit_10_2_split_goal_3 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_10_3 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data_2 )) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.full factors count factor_data_2 )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  EX (factor_data: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i + 1 ) * 10 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (PrimeFactorBagPrefix a (i + 1 ) factor_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data_2 )) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count )),
  TT && emp 
|--
  “ (PrimeFactorBagPrefix a (i + 1 ) factor_data_2 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_10_3_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data_2 )) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count )),
  (PrimeFactorBagPrefix a (i + 1 ) factor_data_2 )
.

Definition solver_entail_wit_10_3_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data_2 )) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_10_4 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.full factors count factor_data_2 )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  EX (factor_data: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i + 1 ) * 10 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (PrimeFactorBagPrefix a (i + 1 ) factor_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  TT && emp 
|--
  “ (PrimeFactorBagPrefix a (i + 1 ) factor_data_2 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_10_4_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  (PrimeFactorBagPrefix a (i + 1 ) factor_data_2 )
.

Definition solver_entail_wit_10_4_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data_2: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (((Znth j prime_data_2 0) * (Znth j prime_data_2 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a 0)) /\ ((Znth k_2 a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data_2 )) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2 )) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2 )) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))
.

Definition solver_entail_wit_11 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : (Permutation factor_data sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data_2)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data_2)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * 10 ))) (PreH18 : (CompletePrimeTable prime_data_2 )) (PreH19 : (PrimeFactorBagPrefix a i factor_data )),
  (IntArray.full factors count sorted_2 )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  EX (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (n_pre * 10 )) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (count + 1 )) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ ((Zlength (sorted)) = count) ”
  &&  “ (increasing sorted ) ”
  &&  “ (PrimeFactorBagPrefix a n_pre sorted ) ”
  &&  “ (DuplicateScanLoopState sorted count 1 0 ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count sorted )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (factor_data: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : (Permutation factor_data sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data_2)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data_2)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * 10 ))) (PreH18 : (CompletePrimeTable prime_data_2 )) (PreH19 : (PrimeFactorBagPrefix a i factor_data )),
  TT && emp 
|--
  “ (DuplicateScanLoopState sorted_2 count 1 0 ) ”
  &&  “ (PrimeFactorBagPrefix a n_pre sorted_2 ) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : (Permutation factor_data sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data_2)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data_2)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * 10 ))) (PreH18 : (CompletePrimeTable prime_data_2 )) (PreH19 : (PrimeFactorBagPrefix a i factor_data )),
  (DuplicateScanLoopState sorted_2 count 1 0 )
.

Definition solver_entail_wit_11_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (factor_data: (@list Z)) (count: Z) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : (Permutation factor_data sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data_2)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data_2)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * 10 ))) (PreH18 : (CompletePrimeTable prime_data_2 )) (PreH19 : (PrimeFactorBagPrefix a i factor_data )),
  (PrimeFactorBagPrefix a n_pre sorted_2 )
.

Definition solver_entail_wit_12 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (ok: Z) (sorted_2: (@list Z)) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : (i >= count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : (0 <= count)) (PreH6 : (count <= (n_pre * 10 ))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1 ))) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : ((Zlength (sorted_2)) = count)) (PreH14 : (increasing sorted_2 )) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted_2 )) (PreH16 : (DuplicateScanLoopState sorted_2 count i ok )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.full factors count sorted_2 )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  EX (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (n_pre * 10 )) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ ((Zlength (sorted)) = count) ”
  &&  “ (increasing sorted ) ”
  &&  “ (PrimeFactorBagPrefix a n_pre sorted ) ”
  &&  “ (DuplicatePrefixState sorted count ok ) ”
  &&  “ (Spec a ok ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count sorted )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (ok: Z) (sorted_2: (@list Z)) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : (i >= count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : (0 <= count)) (PreH6 : (count <= (n_pre * 10 ))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1 ))) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : ((Zlength (sorted_2)) = count)) (PreH14 : (increasing sorted_2 )) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted_2 )) (PreH16 : (DuplicateScanLoopState sorted_2 count i ok )),
  TT && emp 
|--
  “ (Spec a ok ) ”
  &&  “ (DuplicatePrefixState sorted_2 count ok ) ”
  &&  emp
).

Definition solver_entail_wit_12_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (ok: Z) (sorted_2: (@list Z)) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : (i >= count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : (0 <= count)) (PreH6 : (count <= (n_pre * 10 ))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1 ))) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : ((Zlength (sorted_2)) = count)) (PreH14 : (increasing sorted_2 )) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted_2 )) (PreH16 : (DuplicateScanLoopState sorted_2 count i ok )),
  (Spec a ok )
.

Definition solver_entail_wit_12_split_goal_2 :=
forall (a: (@list Z)) (n_pre: Z) (ok: Z) (sorted_2: (@list Z)) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : (i >= count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : (0 <= count)) (PreH6 : (count <= (n_pre * 10 ))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1 ))) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : ((Zlength (sorted_2)) = count)) (PreH14 : (increasing sorted_2 )) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted_2 )) (PreH16 : (DuplicateScanLoopState sorted_2 count i ok )),
  (DuplicatePrefixState sorted_2 count ok )
.

Definition solver_entail_wit_13_1 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (ok: Z) (sorted_2: (@list Z)) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : ((Znth i sorted_2 0) = (Znth (i - 1 ) sorted_2 0))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n_pre * 10 ))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1 ))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2 )) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2 )) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok )),
  (IntArray.full factors count sorted_2 )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  EX (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (n_pre * 10 )) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (count + 1 )) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ ((Zlength (sorted)) = count) ”
  &&  “ (increasing sorted ) ”
  &&  “ (PrimeFactorBagPrefix a n_pre sorted ) ”
  &&  “ (DuplicateScanLoopState sorted count (i + 1 ) 1 ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count sorted )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (ok: Z) (sorted_2: (@list Z)) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : ((Znth i sorted_2 0) = (Znth (i - 1 ) sorted_2 0))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n_pre * 10 ))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1 ))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2 )) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2 )) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok )),
  TT && emp 
|--
  “ (DuplicateScanLoopState sorted_2 count (i + 1 ) 1 ) ”
  &&  emp
).

Definition solver_entail_wit_13_1_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (ok: Z) (sorted_2: (@list Z)) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : ((Znth i sorted_2 0) = (Znth (i - 1 ) sorted_2 0))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n_pre * 10 ))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1 ))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2 )) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2 )) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok )),
  (DuplicateScanLoopState sorted_2 count (i + 1 ) 1 )
.

Definition solver_entail_wit_13_2 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (ok: Z) (sorted_2: (@list Z)) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : ((Znth i sorted_2 0) <> (Znth (i - 1 ) sorted_2 0))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n_pre * 10 ))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1 ))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2 )) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2 )) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok )),
  (IntArray.full factors count sorted_2 )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data_2 )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data_2 )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  EX (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)),
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (n_pre * 10 )) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (count + 1 )) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ ((Zlength (sorted)) = count) ”
  &&  “ (increasing sorted ) ”
  &&  “ (PrimeFactorBagPrefix a n_pre sorted ) ”
  &&  “ (DuplicateScanLoopState sorted count (i + 1 ) ok ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count sorted )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (ok: Z) (sorted_2: (@list Z)) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : ((Znth i sorted_2 0) <> (Znth (i - 1 ) sorted_2 0))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n_pre * 10 ))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1 ))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2 )) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2 )) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok )),
  TT && emp 
|--
  “ (DuplicateScanLoopState sorted_2 count (i + 1 ) ok ) ”
  &&  emp
).

Definition solver_entail_wit_13_2_split_goal_1 :=
forall (a: (@list Z)) (n_pre: Z) (ok: Z) (sorted_2: (@list Z)) (composite_data_2: (@list Z)) (prime_data_2: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : ((Znth i sorted_2 0) <> (Znth (i - 1 ) sorted_2 0))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n_pre * 10 ))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1 ))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : (0 <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2 )) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2 )) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok )),
  (DuplicateScanLoopState sorted_2 count (i + 1 ) ok )
.

Definition solver_entail_wit_14 :=
(
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (prime_data: (@list Z)) (composite_data: (@list Z)) (sorted: (@list Z)) (count: Z) (pc: Z) (ok: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : (0 <= count)) (PreH5 : (count <= (n_pre * 10 ))) (PreH6 : (pc = (Zlength (prime_data)))) (PreH7 : (0 <= pc)) (PreH8 : (pc < 4000)) (PreH9 : ((Zlength (composite_data)) = 31624)) (PreH10 : ((Zlength (sorted)) = count)) (PreH11 : (increasing sorted )) (PreH12 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH13 : (DuplicatePrefixState sorted count ok )) (PreH14 : (Spec a ok )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (Spec a ok ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_full ( &( "primes" ) ) 4000 )
  **  (UCharArray.undef_full ( &( "composite" ) ) 31624 )
) \/
(
forall (a: (@list Z)) (n_pre: Z) (prime_data: (@list Z)) (composite_data: (@list Z)) (sorted: (@list Z)) (count: Z) (pc: Z) (ok: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : (0 <= count)) (PreH5 : (count <= (n_pre * 10 ))) (PreH6 : (pc = (Zlength (prime_data)))) (PreH7 : (0 <= pc)) (PreH8 : (pc < 4000)) (PreH9 : ((Zlength (composite_data)) = 31624)) (PreH10 : ((Zlength (sorted)) = count)) (PreH11 : (increasing sorted )) (PreH12 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH13 : (DuplicatePrefixState sorted count ok )) (PreH14 : (Spec a ok )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  (IntArray.undef_full ( &( "primes" ) ) 4000 )
  **  (UCharArray.undef_full ( &( "composite" ) ) 31624 )
).

Definition solver_entail_wit_14_split_goal_spatial :=
forall (a: (@list Z)) (n_pre: Z) (prime_data: (@list Z)) (composite_data: (@list Z)) (sorted: (@list Z)) (count: Z) (pc: Z) (ok: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : (0 <= count)) (PreH5 : (count <= (n_pre * 10 ))) (PreH6 : (pc = (Zlength (prime_data)))) (PreH7 : (0 <= pc)) (PreH8 : (pc < 4000)) (PreH9 : ((Zlength (composite_data)) = 31624)) (PreH10 : ((Zlength (sorted)) = count)) (PreH11 : (increasing sorted )) (PreH12 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH13 : (DuplicatePrefixState sorted count ok )) (PreH14 : (Spec a ok )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  (IntArray.undef_full ( &( "primes" ) ) 4000 )
  **  (UCharArray.undef_full ( &( "composite" ) ) 31624 )
.

Definition solver_return_wit_1 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (ok: Z) (PreH1 : (Spec a ok )),
  (IntArray.full values_pre n_pre a )
|--
  “ (Spec a ok ) ”
  &&  (IntArray.full values_pre n_pre a )
.

Definition solver_partial_solve_wit_1 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 31624)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (PrimePrefixTable2 i prime_data composite_data )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (i <= 31623) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (2 <= i) ”
  &&  “ (i <= 31624) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (PrimePrefixTable2 i prime_data composite_data ) ”
  &&  (((( &( "composite" ) ) + (i * sizeof(UCHAR)))) # UChar  |-> (Znth i composite_data 0))
  **  (UCharArray.missing_i ( &( "composite" ) ) i 0 31624 composite_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
.

Definition solver_partial_solve_wit_2 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : ((Znth i composite_data 0) = 0)) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data )),
  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
|--
  “ ((Znth i composite_data 0) = 0) ”
  &&  “ (i <= 31623) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (2 <= i) ”
  &&  “ (i <= 31624) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (PrimePrefixTable2 i prime_data composite_data ) ”
  &&  (((( &( "primes" ) ) + (pc * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "primes" ) ) (pc + 1 ) 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
.

Definition solver_partial_solve_wit_3 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (j: Z) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i ) <= j)) (PreH12 : (j <= (31623 + i ))) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data composite_data )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (j <= 31623) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (2 <= i) ”
  &&  “ (i <= 177) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (1 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((i * i ) <= j) ”
  &&  “ (j <= (31623 + i )) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (PrimeMarkTable2 i j prime_data composite_data ) ”
  &&  (((( &( "composite" ) ) + (j * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "composite" ) ) j 0 31624 composite_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
.

Definition solver_partial_solve_wit_4_pure :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 31624)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (PrimePrefixTable2 i prime_data composite_data )),
  ((( &( "factors" ) )) # Ptr  |->_)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (0 <= (n_pre * 10 )) ”
  &&  “ (((n_pre * 10 ) * sizeof(INT) ) <= UINT_MAX) ”
  &&  “ (((n_pre * 10 ) * sizeof(INT) ) = ((n_pre * 10 ) * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_4_aux :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 31624)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (PrimePrefixTable2 i prime_data composite_data )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
|--
  “ (0 <= (n_pre * 10 )) ”
  &&  “ (((n_pre * 10 ) * sizeof(INT) ) <= UINT_MAX) ”
  &&  “ (((n_pre * 10 ) * sizeof(INT) ) = ((n_pre * 10 ) * sizeof(INT) )) ”
  &&  “ (i > 31623) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (2 <= i) ”
  &&  “ (i <= 31624) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (PrimePrefixTable2 i prime_data composite_data ) ”
  &&  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (count = (Zlength (factor_data)))) (PreH13 : (0 <= count)) (PreH14 : (count <= (i * 10 ))) (PreH15 : (CompletePrimeTable prime_data )) (PreH16 : (PrimeFactorBagPrefix a i factor_data )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (i * 10 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (PrimeFactorBagPrefix a i factor_data ) ”
  &&  (((values_pre + (i * sizeof(INT)))) # Int  |-> (Znth i a 0))
  **  (IntArray.missing_i values_pre i 0 n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
.

Definition solver_partial_solve_wit_6 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (0 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorScanState a prime_data i j x factor_data )) (PreH21 : (FactorScanState2 a prime_data i j x factor_data )) (PreH22 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (j < pc) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorScanState a prime_data i j x factor_data ) ”
  &&  “ (FactorScanState2 a prime_data i j x factor_data ) ”
  &&  “ (FactorAppendCapacity prime_data i j x count ) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j prime_data 0))
  **  (IntArray.missing_i ( &( "primes" ) ) j 0 pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
.

Definition solver_partial_solve_wit_7 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (0 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorScanState a prime_data i j x factor_data )) (PreH21 : (FactorScanState2 a prime_data i j x factor_data )) (PreH22 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (j < pc) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorScanState a prime_data i j x factor_data ) ”
  &&  “ (FactorScanState2 a prime_data i j x factor_data ) ”
  &&  “ (FactorAppendCapacity prime_data i j x count ) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j prime_data 0))
  **  (IntArray.missing_i ( &( "primes" ) ) j 0 pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
.

Definition solver_partial_solve_wit_8 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x) ”
  &&  “ (j < pc) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorScanState a prime_data i j x factor_data ) ”
  &&  “ (FactorScanState2 a prime_data i j x factor_data ) ”
  &&  “ (FactorAppendCapacity prime_data i j x count ) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j prime_data 0))
  **  (IntArray.missing_i ( &( "primes" ) ) j 0 pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
.

Definition solver_partial_solve_wit_9 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data 0) ) ) = 0)) (PreH2 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data )) (PreH22 : (FactorScanState a prime_data i j x factor_data )) (PreH23 : (FactorScanState2 a prime_data i j x factor_data )) (PreH24 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x % ( (Znth j prime_data 0) ) ) = 0) ”
  &&  “ (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x) ”
  &&  “ (j < pc) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorScanState a prime_data i j x factor_data ) ”
  &&  “ (FactorScanState2 a prime_data i j x factor_data ) ”
  &&  “ (FactorAppendCapacity prime_data i j x count ) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j prime_data 0))
  **  (IntArray.missing_i ( &( "primes" ) ) j 0 pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
.

Definition solver_partial_solve_wit_10 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data 0) ) ) = 0)) (PreH2 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data )) (PreH22 : (FactorScanState a prime_data i j x factor_data )) (PreH23 : (FactorScanState2 a prime_data i j x factor_data )) (PreH24 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x % ( (Znth j prime_data 0) ) ) = 0) ”
  &&  “ (((Znth j prime_data 0) * (Znth j prime_data 0) ) <= x) ”
  &&  “ (j < pc) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorScanState a prime_data i j x factor_data ) ”
  &&  “ (FactorScanState2 a prime_data i j x factor_data ) ”
  &&  “ (FactorAppendCapacity prime_data i j x count ) ”
  &&  (((factors + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
.

Definition solver_partial_solve_wit_11 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : (0 <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10 ) + 9 ))) (PreH18 : (CompletePrimeTable prime_data )) (PreH19 : (FactorDivideState a prime_data i j x factor_data )) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorDivideState a prime_data i j x factor_data ) ”
  &&  “ (FactorDivideState2 a prime_data i j x factor_data ) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j prime_data 0))
  **  (IntArray.missing_i ( &( "primes" ) ) j 0 pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
.

Definition solver_partial_solve_wit_12 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : ((x % ( (Znth j prime_data 0) ) ) = 0)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : (0 <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10 ) + 9 ))) (PreH19 : (CompletePrimeTable prime_data )) (PreH20 : (FactorDivideState a prime_data i j x factor_data )) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ ((x % ( (Znth j prime_data 0) ) ) = 0) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorDivideState a prime_data i j x factor_data ) ”
  &&  “ (FactorDivideState2 a prime_data i j x factor_data ) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j prime_data 0))
  **  (IntArray.missing_i ( &( "primes" ) ) j 0 pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
.

Definition solver_partial_solve_wit_13 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : (0 <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : (0 <= count)) (PreH19 : (count <= ((i * 10 ) + 9 ))) (PreH20 : (CompletePrimeTable prime_data )) (PreH21 : (FactorScanState a prime_data i j x factor_data )) (PreH22 : (FactorScanState2 a prime_data i j x factor_data )) (PreH23 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (x > 1) ”
  &&  “ (j >= pc) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorScanState a prime_data i j x factor_data ) ”
  &&  “ (FactorScanState2 a prime_data i j x factor_data ) ”
  &&  “ (FactorAppendCapacity prime_data i j x count ) ”
  &&  (((factors + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
.

Definition solver_partial_solve_wit_14 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (x: Z) (pc: Z) (j: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data 0) * (Znth j prime_data 0) ) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : (0 <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : (0 <= count)) (PreH20 : (count <= ((i * 10 ) + 9 ))) (PreH21 : (CompletePrimeTable prime_data )) (PreH22 : (FactorScanState a prime_data i j x factor_data )) (PreH23 : (FactorScanState2 a prime_data i j x factor_data )) (PreH24 : (FactorAppendCapacity prime_data i j x count )),
  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (x > 1) ”
  &&  “ (((Znth j prime_data 0) * (Znth j prime_data 0) ) > x) ”
  &&  “ (j < pc) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= pc) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= 1000000000) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i * 10 ) + 9 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (FactorScanState a prime_data i j x factor_data ) ”
  &&  “ (FactorScanState2 a prime_data i j x factor_data ) ”
  &&  “ (FactorAppendCapacity prime_data i j x count ) ”
  &&  (((factors + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg factors (count + 1 ) (n_pre * 10 ) )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
.

Definition solver_partial_solve_wit_15_pure :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (count = (Zlength (factor_data)))) (PreH13 : (0 <= count)) (PreH14 : (count <= (i * 10 ))) (PreH15 : (CompletePrimeTable prime_data )) (PreH16 : (PrimeFactorBagPrefix a i factor_data )),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (count = (Zlength (factor_data))) ”
  &&  “ (sizeof(INT) = sizeof(INT)) ”
.

Definition solver_partial_solve_wit_15_aux :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (factor_data: (@list Z)) (count: Z) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (0 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (count = (Zlength (factor_data)))) (PreH13 : (0 <= count)) (PreH14 : (count <= (i * 10 ))) (PreH15 : (CompletePrimeTable prime_data )) (PreH16 : (PrimeFactorBagPrefix a i factor_data )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count factor_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (count = (Zlength (factor_data))) ”
  &&  “ (sizeof(INT) = sizeof(INT)) ”
  &&  “ (i >= n_pre) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (a)))) -> ((1 <= (Znth k a 0)) /\ ((Znth k a 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ (count = (Zlength (factor_data))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (i * 10 )) ”
  &&  “ (CompletePrimeTable prime_data ) ”
  &&  “ (PrimeFactorBagPrefix a i factor_data ) ”
  &&  (IntArray.full factors count factor_data )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
.

Definition solver_partial_solve_wit_15 := solver_partial_solve_wit_15_pure -> solver_partial_solve_wit_15_aux.

Definition solver_partial_solve_wit_16 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (ok: Z) (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : (i < count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : (0 <= count)) (PreH6 : (count <= (n_pre * 10 ))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1 ))) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : ((Zlength (sorted)) = count)) (PreH14 : (increasing sorted )) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH16 : (DuplicateScanLoopState sorted count i ok )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count sorted )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (i < count) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (n_pre * 10 )) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (count + 1 )) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ ((Zlength (sorted)) = count) ”
  &&  “ (increasing sorted ) ”
  &&  “ (PrimeFactorBagPrefix a n_pre sorted ) ”
  &&  “ (DuplicateScanLoopState sorted count i ok ) ”
  &&  (((factors + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i factors i 0 count sorted )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
.

Definition solver_partial_solve_wit_17 :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (factors: Z) (ok: Z) (sorted: (@list Z)) (composite_data: (@list Z)) (prime_data: (@list Z)) (pc: Z) (i: Z) (count: Z) (PreH1 : (i < count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : (0 <= count)) (PreH6 : (count <= (n_pre * 10 ))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1 ))) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : (0 <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : ((Zlength (sorted)) = count)) (PreH14 : (increasing sorted )) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH16 : (DuplicateScanLoopState sorted count i ok )),
  (IntArray.full factors count sorted )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (i < count) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (n_pre * 10 )) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (count + 1 )) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ ((Zlength (sorted)) = count) ”
  &&  “ (increasing sorted ) ”
  &&  “ (PrimeFactorBagPrefix a n_pre sorted ) ”
  &&  “ (DuplicateScanLoopState sorted count i ok ) ”
  &&  (((factors + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) sorted 0))
  **  (IntArray.missing_i factors (i - 1 ) 0 count sorted )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
.

Definition solver_partial_solve_wit_18_pure :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (prime_data: (@list Z)) (composite_data: (@list Z)) (sorted: (@list Z)) (count: Z) (pc: Z) (ok: Z) (factors: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : (0 <= count)) (PreH5 : (count <= (n_pre * 10 ))) (PreH6 : (pc = (Zlength (prime_data)))) (PreH7 : (0 <= pc)) (PreH8 : (pc < 4000)) (PreH9 : ((Zlength (composite_data)) = 31624)) (PreH10 : ((Zlength (sorted)) = count)) (PreH11 : (increasing sorted )) (PreH12 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH13 : (DuplicatePrefixState sorted count ok )) (PreH14 : (Spec a ok )),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "pc" ) )) # Int  |-> pc)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  ((( &( "factors" ) )) # Ptr  |-> factors)
  **  (IntArray.full factors count sorted )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (0 <= count) ”
  &&  “ (count <= (n_pre * 10 )) ”
  &&  “ ((Zlength (sorted)) = count) ”
.

Definition solver_partial_solve_wit_18_aux :=
forall (a: (@list Z)) (values_pre: Z) (n_pre: Z) (prime_data: (@list Z)) (composite_data: (@list Z)) (sorted: (@list Z)) (count: Z) (pc: Z) (ok: Z) (factors: Z) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : (0 <= count)) (PreH5 : (count <= (n_pre * 10 ))) (PreH6 : (pc = (Zlength (prime_data)))) (PreH7 : (0 <= pc)) (PreH8 : (pc < 4000)) (PreH9 : ((Zlength (composite_data)) = 31624)) (PreH10 : ((Zlength (sorted)) = count)) (PreH11 : (increasing sorted )) (PreH12 : (PrimeFactorBagPrefix a n_pre sorted )) (PreH13 : (DuplicatePrefixState sorted count ok )) (PreH14 : (Spec a ok )),
  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
  **  (IntArray.full factors count sorted )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
|--
  “ (0 <= count) ”
  &&  “ (count <= (n_pre * 10 )) ”
  &&  “ ((Zlength (sorted)) = count) ”
  &&  “ (n_pre = (Zlength (a))) ”
  &&  “ (2 <= (Zlength (a))) ”
  &&  “ ((Zlength (a)) <= 100000) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (n_pre * 10 )) ”
  &&  “ (pc = (Zlength (prime_data))) ”
  &&  “ (0 <= pc) ”
  &&  “ (pc < 4000) ”
  &&  “ ((Zlength (composite_data)) = 31624) ”
  &&  “ ((Zlength (sorted)) = count) ”
  &&  “ (increasing sorted ) ”
  &&  “ (PrimeFactorBagPrefix a n_pre sorted ) ”
  &&  “ (DuplicatePrefixState sorted count ok ) ”
  &&  “ (Spec a ok ) ”
  &&  (IntArray.full factors count sorted )
  **  (IntArray.undef_seg factors count (n_pre * 10 ) )
  **  (IntArray.full values_pre n_pre a )
  **  (IntArray.full ( &( "primes" ) ) pc prime_data )
  **  (IntArray.undef_seg ( &( "primes" ) ) pc 4000 )
  **  (UCharArray.full ( &( "composite" ) ) 31624 composite_data )
.

Definition solver_partial_solve_wit_18 := solver_partial_solve_wit_18_pure -> solver_partial_solve_wit_18_aux.

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
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Axiom proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Axiom proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Axiom proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15_pure : solver_partial_solve_wit_15_pure.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18_pure : solver_partial_solve_wit_18_pure.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.

End VC_Correct.
