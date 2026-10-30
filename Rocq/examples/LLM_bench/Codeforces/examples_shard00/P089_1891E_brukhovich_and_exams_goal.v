From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P089_1891E_brukhovich_and_exams_lib.
Local Open Scope sac.

(*----- Function gcdll -----*)

Definition gcdll_safety_wit_1 :=
forall (a_pre: Z) (b_pre: Z) (g: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : (GcdResult a b g )) (PreH6 : (GcdResult a_pre b_pre g )) (PreH7 : (b <> 0)),
  ((( &( "t" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "b" ) )) # Int64  |-> b)
|--
  “ ((a <> (INT64_MIN)) \/ (b <> (-1))) ”
  &&  “ (b <> 0) ”
.

Definition gcdll_entail_wit_1 :=
(
forall (a_pre: Z) (b_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)),
  TT && emp 
|--
  EX (g: Z),
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 1000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 1000000000) ”
  &&  “ (GcdResult a_pre b_pre g ) ”
  &&  “ (GcdResult a_pre b_pre g ) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 1000000000)),
  TT && emp 
|--
  EX (g: Z),
  “ (GcdResult a_pre b_pre g ) ”
  &&  “ (GcdResult a_pre b_pre g ) ”
  &&  emp
).

Definition gcdll_entail_wit_2 :=
(
forall (a_pre: Z) (b_pre: Z) (g_2: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : (GcdResult a b g_2 )) (PreH6 : (GcdResult a_pre b_pre g_2 )) (PreH7 : (b <> 0)),
  TT && emp 
|--
  EX (g: Z),
  “ (0 <= b) ”
  &&  “ (b <= 1000000000) ”
  &&  “ (0 <= (a % ( b ) )) ”
  &&  “ ((a % ( b ) ) <= 1000000000) ”
  &&  “ (GcdResult b (a % ( b ) ) g ) ”
  &&  “ (GcdResult a_pre b_pre g ) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (g_2: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : (GcdResult a b g_2 )) (PreH6 : (GcdResult a_pre b_pre g_2 )) (PreH7 : (b <> 0)),
  TT && emp 
|--
  EX (g: Z),
  “ (0 <= (a % ( b ) )) ”
  &&  “ ((a % ( b ) ) <= 1000000000) ”
  &&  “ (GcdResult b (a % ( b ) ) g ) ”
  &&  “ (GcdResult a_pre b_pre g ) ”
  &&  emp
).

Definition gcdll_return_wit_1 :=
(
forall (a_pre: Z) (b_pre: Z) (g: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : (GcdResult a b g )) (PreH6 : (GcdResult a_pre b_pre g )) (PreH7 : (b = 0)),
  TT && emp 
|--
  “ (GcdResult a_pre b_pre a ) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (g: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : (GcdResult a b g )) (PreH6 : (GcdResult a_pre b_pre g )) (PreH7 : (b = 0)),
  TT && emp 
|--
  “ (GcdResult a_pre b_pre a ) ”
  &&  emp
).

Definition gcdll_return_wit_1_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (g: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : (GcdResult a b g )) (PreH6 : (GcdResult a_pre b_pre g )) (PreH7 : (b = 0)),
  (GcdResult a_pre b_pre a )
.

(*----- Function cmpi -----*)

Definition cmpi_safety_wit_1 :=
forall (y: Z) (x: Z) (A_pre: Z) (B_pre: Z) (PreH1 : (0 <= x)) (PreH2 : (x <= 100000)) (PreH3 : (0 <= y)) (PreH4 : (y <= 100000)),
  ((( &( "A" ) )) # Ptr  |-> A_pre)
  **  ((( &( "B" ) )) # Ptr  |-> B_pre)
  **  ((A_pre) # Int  |-> x)
  **  ((B_pre) # Int  |-> y)
|--
  “ ((x - y ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x - y )) ”
.

Definition cmpi_return_wit_1 :=
forall (y: Z) (x: Z) (A_pre: Z) (B_pre: Z) (PreH1 : (0 <= x)) (PreH2 : (x <= 100000)) (PreH3 : (0 <= y)) (PreH4 : (y <= 100000)),
  ((A_pre) # Int  |-> x)
  **  ((B_pre) # Int  |-> y)
|--
  “ ((x - y ) = (x - y )) ”
  &&  ((A_pre) # Int  |-> x)
  **  ((B_pre) # Int  |-> y)
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH5 : (n_pre = (Zlength (values)))),
  ((( &( "allone" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH5 : (n_pre = (Zlength (values)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "allone" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= allone)) (PreH10 : (allone <= 1)) (PreH11 : (AllOnePrefix values i allone )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "allone" ) )) # Int  |-> allone)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "allone" ) )) # Int  |-> allone)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "allone" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "allone" ) )) # Int  |-> allone)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : (k_pre = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )) (PreH13 : (allone <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : (k_pre <> n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )) (PreH13 : (allone <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((n_pre - k_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - k_pre )) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= allone)) (PreH10 : (allone <= 1)) (PreH11 : (AllOnePrefix values i allone )) (PreH12 : (allone = 0)),
  ((( &( "two" ) )) # Int  |->_)
  **  ((( &( "sad" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= allone)) (PreH10 : (allone <= 1)) (PreH11 : (AllOnePrefix values i allone )) (PreH12 : (allone = 0)),
  ((( &( "sad" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= allone)) (PreH10 : (allone <= 1)) (PreH11 : (AllOnePrefix values i allone )) (PreH12 : (allone = 0)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "two" ) )) # Int  |-> 0)
  **  ((( &( "sad" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH6 : (allone = 0)) (PreH7 : (two = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (0 <= sad)) (PreH12 : (sad <= i)) (PreH13 : (CoprimeEdgePrefixCount values i sad )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH6 : (allone = 0)) (PreH7 : (two = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (0 <= sad)) (PreH12 : (sad <= i)) (PreH13 : (CoprimeEdgePrefixCount values i sad )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (two = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (0 <= sad)) (PreH13 : (sad <= i)) (PreH14 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (two = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (0 <= sad)) (PreH13 : (sad <= i)) (PreH14 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (retval: Z) (PreH1 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (two = 0)) (PreH10 : (AllOnePrefix values n_pre allone )) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (0 <= sad)) (PreH14 : (sad <= i)) (PreH15 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (two = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (0 <= sad)) (PreH15 : (sad <= i)) (PreH16 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
|--
  “ ((sad + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sad + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (two = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (0 <= sad)) (PreH15 : (sad <= i)) (PreH16 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> (sad + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (two = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (0 <= sad)) (PreH15 : (sad <= i)) (PreH16 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (two = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (0 <= sad)) (PreH13 : (sad <= i)) (PreH14 : (CoprimeEdgePrefixCount values i sad )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_21 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (allone: Z) (PreH1 : (n_pre < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= n_pre)) (PreH16 : (PairSavingsPrefix values n_pre two )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> n_pre)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ False ”
.

Definition solver_safety_wit_22 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : (i = 0)) (PreH17 : (PairSavingsPrefix values i two )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ False ”
.

Definition solver_safety_wit_23 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth (i - 1 ) values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth i values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_25 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : (i = 0)) (PreH17 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_26 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : ((Znth i values 0) = 1)) (PreH18 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
|--
  “ False ”
.

Definition solver_safety_wit_27 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : ((Znth (i - 1 ) values 0) = 1)) (PreH18 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_28 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : ((Znth i values 0) = 1)) (PreH18 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_29 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : (i = 0)) (PreH18 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_30 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : ((Znth (i - 1 ) values 0) = 1)) (PreH18 : (PairSavingsPrefix values i two )),
  ((( &( "run" ) )) # Int  |->_)
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_31 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : (i = 0)) (PreH18 : (PairSavingsPrefix values i two )),
  ((( &( "run" ) )) # Int  |->_)
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_32 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH6 : (allone = 0)) (PreH7 : (AllOnePrefix values n_pre allone )) (PreH8 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH9 : (0 <= sad)) (PreH10 : (sad < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= two)) (PreH14 : (0 <= run)) (PreH15 : (run <= (i + 1 ))) (PreH16 : (PairRunSuffix values (i + 1 ) run )) (PreH17 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH18 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_33 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH6 : (allone = 0)) (PreH7 : (AllOnePrefix values n_pre allone )) (PreH8 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH9 : (0 <= sad)) (PreH10 : (sad < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= two)) (PreH14 : (0 <= run)) (PreH15 : (run <= (i + 1 ))) (PreH16 : (PairRunSuffix values (i + 1 ) run )) (PreH17 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH18 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_34 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_35 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_36 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_37 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) <> 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_38 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) <> 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_39 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH2 : ((Znth (i + 1 ) values 0) <> 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (AllOnePrefix values n_pre allone )) (PreH11 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH12 : (0 <= sad)) (PreH13 : (sad < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= two)) (PreH17 : (0 <= run)) (PreH18 : (run <= (i + 1 ))) (PreH19 : (PairRunSuffix values (i + 1 ) run )) (PreH20 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH21 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_40 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((run + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (run + 1 )) ”
.

Definition solver_safety_wit_41 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((two + (run ÷ 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (two + (run ÷ 2 ) )) ”
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((two + (run ÷ 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (two + (run ÷ 2 ) )) ”
).

Definition solver_safety_wit_41_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((two + (run ÷ 2 ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_41_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((INT_MIN) <= (two + (run ÷ 2 ) )) ”
.

Definition solver_safety_wit_42 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((run <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_43 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_44 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> (two + (run ÷ 2 ) ))
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_45 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> (run + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_46 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> (two + (run ÷ 2 ) ))
  **  ((( &( "run" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_47 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((two + (run ÷ 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (two + (run ÷ 2 ) )) ”
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((two + (run ÷ 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (two + (run ÷ 2 ) )) ”
).

Definition solver_safety_wit_47_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((two + (run ÷ 2 ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_47_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((INT_MIN) <= (two + (run ÷ 2 ) )) ”
.

Definition solver_safety_wit_48 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((run <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_49 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_50 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) = 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((two + (run ÷ 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (two + (run ÷ 2 ) )) ”
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) = 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((two + (run ÷ 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (two + (run ÷ 2 ) )) ”
).

Definition solver_safety_wit_50_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) = 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((two + (run ÷ 2 ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_50_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) = 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((INT_MIN) <= (two + (run ÷ 2 ) )) ”
.

Definition solver_safety_wit_51 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) = 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((run <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_52 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) = 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_53 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> (two + (run ÷ 2 ) ))
  **  ((( &( "run" ) )) # Int  |-> run)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_54 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) = 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> (two + (run ÷ 2 ) ))
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_55 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (sad: Z) (two: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (PairSavingsPrefix values n_pre two )) (PreH11 : (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) )) (PreH12 : (0 <= sad)) (PreH13 : (sad < n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= n_pre)),
  ((( &( "oc" ) )) # Int  |->_)
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "ones" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_56 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (sad: Z) (two: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (PairSavingsPrefix values n_pre two )) (PreH11 : (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) )) (PreH12 : (0 <= sad)) (PreH13 : (sad < n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= n_pre)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "oc" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "ones" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_57 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (n_pre < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= n_pre)) (PreH14 : ((Zlength (blocks)) = oc)) (PreH15 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH16 : (PairSavingsPrefix values n_pre two )) (PreH17 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH18 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH19 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH20 : (0 <= sad)) (PreH21 : (sad < n_pre)) (PreH22 : (0 <= two)) (PreH23 : ((2 * two ) <= n_pre)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "i" ) )) # Int  |-> n_pre)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_58 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks)) = oc)) (PreH15 : (i = 0)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH19 : (JointPairBlockPrefix values i sad two blocks )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_59 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks)) = oc)) (PreH15 : ((Znth (i - 1 ) values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH19 : (JointPairBlockPrefix values i sad two blocks )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_60 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks)) = oc)) (PreH15 : ((Znth i values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH19 : (JointPairBlockPrefix values i sad two blocks )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_61 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks)) = oc)) (PreH15 : (i = 0)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH19 : (JointPairBlockPrefix values i sad two blocks )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_62 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= i)) (PreH15 : ((Zlength (blocks)) = oc)) (PreH16 : ((Znth i values 0) <> 1)) (PreH17 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH18 : (PairSavingsPrefix values n_pre two )) (PreH19 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH20 : (JointPairBlockPrefix values i sad two blocks )) (PreH21 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH22 : (0 <= sad)) (PreH23 : (sad < n_pre)) (PreH24 : (0 <= two)) (PreH25 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_63 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= i)) (PreH15 : ((Zlength (blocks)) = oc)) (PreH16 : ((Znth (i - 1 ) values 0) <> 1)) (PreH17 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH18 : (PairSavingsPrefix values n_pre two )) (PreH19 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH20 : (JointPairBlockPrefix values i sad two blocks )) (PreH21 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH22 : (0 <= sad)) (PreH23 : (sad < n_pre)) (PreH24 : (0 <= two)) (PreH25 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_64 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= i)) (PreH15 : ((Zlength (blocks)) = oc)) (PreH16 : ((Znth i values 0) <> 1)) (PreH17 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH18 : (PairSavingsPrefix values n_pre two )) (PreH19 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH20 : (JointPairBlockPrefix values i sad two blocks )) (PreH21 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH22 : (0 <= sad)) (PreH23 : (sad < n_pre)) (PreH24 : (0 <= two)) (PreH25 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_65 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= i)) (PreH15 : ((Zlength (blocks)) = oc)) (PreH16 : (i = 0)) (PreH17 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH18 : (PairSavingsPrefix values n_pre two )) (PreH19 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH20 : (JointPairBlockPrefix values i sad two blocks )) (PreH21 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH22 : (0 <= sad)) (PreH23 : (sad < n_pre)) (PreH24 : (0 <= two)) (PreH25 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_66 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= l)) (PreH11 : (l <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= l)) (PreH15 : ((Zlength (blocks)) = oc)) (PreH16 : ((Znth (l - 1 ) values 0) <> 1)) (PreH17 : ((Znth l values 0) = 1)) (PreH18 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH19 : (PairSavingsPrefix values n_pre two )) (PreH20 : (CanonicalOneRunScanState values l i blocks )) (PreH21 : (JointPairBlockPrefix values l sad two blocks )) (PreH22 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH23 : (0 <= sad)) (PreH24 : (sad < n_pre)) (PreH25 : (0 <= two)) (PreH26 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_67 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= l)) (PreH11 : (l <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= l)) (PreH15 : ((Zlength (blocks)) = oc)) (PreH16 : (l = 0)) (PreH17 : ((Znth l values 0) = 1)) (PreH18 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH19 : (PairSavingsPrefix values n_pre two )) (PreH20 : (CanonicalOneRunScanState values l i blocks )) (PreH21 : (JointPairBlockPrefix values l sad two blocks )) (PreH22 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH23 : (0 <= sad)) (PreH24 : (sad < n_pre)) (PreH25 : (0 <= two)) (PreH26 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_68 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= l)) (PreH12 : (l <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= oc)) (PreH15 : (oc <= l)) (PreH16 : ((Zlength (blocks)) = oc)) (PreH17 : (l = 0)) (PreH18 : ((Znth l values 0) = 1)) (PreH19 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH20 : (PairSavingsPrefix values n_pre two )) (PreH21 : (CanonicalOneRunScanState values l i blocks )) (PreH22 : (JointPairBlockPrefix values l sad two blocks )) (PreH23 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_69 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= l)) (PreH12 : (l <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= oc)) (PreH15 : (oc <= l)) (PreH16 : ((Zlength (blocks)) = oc)) (PreH17 : ((Znth (l - 1 ) values 0) <> 1)) (PreH18 : ((Znth l values 0) = 1)) (PreH19 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH20 : (PairSavingsPrefix values n_pre two )) (PreH21 : (CanonicalOneRunScanState values l i blocks )) (PreH22 : (JointPairBlockPrefix values l sad two blocks )) (PreH23 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_70 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= l)) (PreH11 : (l <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= l)) (PreH15 : ((Zlength (blocks)) = oc)) (PreH16 : ((Znth (l - 1 ) values 0) <> 1)) (PreH17 : ((Znth l values 0) = 1)) (PreH18 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH19 : (PairSavingsPrefix values n_pre two )) (PreH20 : (CanonicalOneRunScanState values l i blocks )) (PreH21 : (JointPairBlockPrefix values l sad two blocks )) (PreH22 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH23 : (0 <= sad)) (PreH24 : (sad < n_pre)) (PreH25 : (0 <= two)) (PreH26 : ((2 * two ) <= n_pre)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_71 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= l)) (PreH11 : (l <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= l)) (PreH15 : ((Zlength (blocks)) = oc)) (PreH16 : (l = 0)) (PreH17 : ((Znth l values 0) = 1)) (PreH18 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH19 : (PairSavingsPrefix values n_pre two )) (PreH20 : (CanonicalOneRunScanState values l i blocks )) (PreH21 : (JointPairBlockPrefix values l sad two blocks )) (PreH22 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH23 : (0 <= sad)) (PreH24 : (sad < n_pre)) (PreH25 : (0 <= two)) (PreH26 : ((2 * two ) <= n_pre)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_72 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= l)) (PreH12 : (l <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= oc)) (PreH15 : (oc <= l)) (PreH16 : ((Zlength (blocks)) = oc)) (PreH17 : (l = 0)) (PreH18 : ((Znth l values 0) = 1)) (PreH19 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH20 : (PairSavingsPrefix values n_pre two )) (PreH21 : (CanonicalOneRunScanState values l i blocks )) (PreH22 : (JointPairBlockPrefix values l sad two blocks )) (PreH23 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_73 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= l)) (PreH12 : (l <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= oc)) (PreH15 : (oc <= l)) (PreH16 : ((Zlength (blocks)) = oc)) (PreH17 : ((Znth (l - 1 ) values 0) <> 1)) (PreH18 : ((Znth l values 0) = 1)) (PreH19 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH20 : (PairSavingsPrefix values n_pre two )) (PreH21 : (CanonicalOneRunScanState values l i blocks )) (PreH22 : (JointPairBlockPrefix values l sad two blocks )) (PreH23 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_74 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (l > 0)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= l)) (PreH12 : (l <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= oc)) (PreH15 : (oc <= l)) (PreH16 : ((Zlength (blocks)) = oc)) (PreH17 : (l = 0)) (PreH18 : ((Znth l values 0) = 1)) (PreH19 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH20 : (PairSavingsPrefix values n_pre two )) (PreH21 : (CanonicalOneRunScanState values l i blocks )) (PreH22 : (JointPairBlockPrefix values l sad two blocks )) (PreH23 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_75 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (l > 0)) (PreH2 : ((Znth i values 0) <> 1)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (AllOnePrefix values n_pre allone )) (PreH11 : (ones <> 0)) (PreH12 : (0 <= l)) (PreH13 : (l <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= oc)) (PreH16 : (oc <= l)) (PreH17 : ((Zlength (blocks)) = oc)) (PreH18 : (l = 0)) (PreH19 : ((Znth l values 0) = 1)) (PreH20 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH21 : (PairSavingsPrefix values n_pre two )) (PreH22 : (CanonicalOneRunScanState values l i blocks )) (PreH23 : (JointPairBlockPrefix values l sad two blocks )) (PreH24 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH25 : (0 <= sad)) (PreH26 : (sad < n_pre)) (PreH27 : (0 <= two)) (PreH28 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_76 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (l > 0)) (PreH3 : ((Znth i values 0) <> 1)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (ones <> 0)) (PreH13 : (0 <= l)) (PreH14 : (l <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= oc)) (PreH17 : (oc <= l)) (PreH18 : ((Zlength (blocks)) = oc)) (PreH19 : ((Znth (l - 1 ) values 0) <> 1)) (PreH20 : ((Znth l values 0) = 1)) (PreH21 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH22 : (PairSavingsPrefix values n_pre two )) (PreH23 : (CanonicalOneRunScanState values l i blocks )) (PreH24 : (JointPairBlockPrefix values l sad two blocks )) (PreH25 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH26 : (0 <= sad)) (PreH27 : (sad < n_pre)) (PreH28 : (0 <= two)) (PreH29 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_77 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (l > 0)) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (AllOnePrefix values n_pre allone )) (PreH11 : (ones <> 0)) (PreH12 : (0 <= l)) (PreH13 : (l <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= oc)) (PreH16 : (oc <= l)) (PreH17 : ((Zlength (blocks)) = oc)) (PreH18 : ((Znth (l - 1 ) values 0) <> 1)) (PreH19 : ((Znth l values 0) = 1)) (PreH20 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH21 : (PairSavingsPrefix values n_pre two )) (PreH22 : (CanonicalOneRunScanState values l i blocks )) (PreH23 : (JointPairBlockPrefix values l sad two blocks )) (PreH24 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH25 : (0 <= sad)) (PreH26 : (sad < n_pre)) (PreH27 : (0 <= two)) (PreH28 : ((2 * two ) <= n_pre)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_78 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (l > 0)) (PreH3 : ((Znth i values 0) <> 1)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (ones <> 0)) (PreH13 : (0 <= l)) (PreH14 : (l <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= oc)) (PreH17 : (oc <= l)) (PreH18 : ((Zlength (blocks)) = oc)) (PreH19 : ((Znth (l - 1 ) values 0) <> 1)) (PreH20 : ((Znth l values 0) = 1)) (PreH21 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH22 : (PairSavingsPrefix values n_pre two )) (PreH23 : (CanonicalOneRunScanState values l i blocks )) (PreH24 : (JointPairBlockPrefix values l sad two blocks )) (PreH25 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH26 : (0 <= sad)) (PreH27 : (sad < n_pre)) (PreH28 : (0 <= two)) (PreH29 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((i - l ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - l )) ”
.

Definition solver_safety_wit_79 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (l > 0)) (PreH3 : ((Znth i values 0) <> 1)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (ones <> 0)) (PreH13 : (0 <= l)) (PreH14 : (l <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= oc)) (PreH17 : (oc <= l)) (PreH18 : ((Zlength (blocks)) = oc)) (PreH19 : ((Znth (l - 1 ) values 0) <> 1)) (PreH20 : ((Znth l values 0) = 1)) (PreH21 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH22 : (PairSavingsPrefix values n_pre two )) (PreH23 : (CanonicalOneRunScanState values l i blocks )) (PreH24 : (JointPairBlockPrefix values l sad two blocks )) (PreH25 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH26 : (0 <= sad)) (PreH27 : (sad < n_pre)) (PreH28 : (0 <= two)) (PreH29 : ((2 * two ) <= n_pre)),
  (IntArray.seg ones 0 (oc + 1 ) (app (blocks) ((cons ((i - l )) ((@nil Z))))) )
  **  (IntArray.undef_seg ones (oc + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
|--
  “ ((oc + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (oc + 1 )) ”
.

Definition solver_safety_wit_80 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre < two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "use" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((sad - (2 * k_pre ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sad - (2 * k_pre ) )) ”
.

Definition solver_safety_wit_81 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre < two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "use" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((2 * k_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * k_pre )) ”
.

Definition solver_safety_wit_82 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre < two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "use" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_83 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre >= two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "use" ) )) # Int  |-> two)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((sad - (2 * two ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sad - (2 * two ) )) ”
.

Definition solver_safety_wit_84 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre >= two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "use" ) )) # Int  |-> two)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((2 * two ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * two )) ”
.

Definition solver_safety_wit_85 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre >= two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "use" ) )) # Int  |-> two)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_86 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre < two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "use" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> (sad - (2 * k_pre ) ))
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((k_pre - k_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k_pre - k_pre )) ”
.

Definition solver_safety_wit_87 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre >= two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "use" ) )) # Int  |-> two)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> (sad - (2 * two ) ))
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((k_pre - two ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k_pre - two )) ”
.

Definition solver_safety_wit_88 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (sorted: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (two: Z) (sad: Z) (use: Z) (k: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (allone = 0)) (PreH6 : (ones <> 0)) (PreH7 : (0 <= oc)) (PreH8 : (oc <= n_pre)) (PreH9 : ((Zlength (blocks)) = oc)) (PreH10 : ((Zlength (sorted)) = oc)) (PreH11 : (Permutation blocks sorted )) (PreH12 : (increasing sorted )) (PreH13 : (ExamOptimizationSummary values (sad + (2 * use ) ) two blocks )) (PreH14 : (OptimizationSafetyBounds (sad + (2 * use ) ) two blocks )) (PreH15 : (MinValue k_pre two use )) (PreH16 : (k = (k_pre - use ))) (PreH17 : (sad = ((sad + (2 * use ) ) - (2 * use ) ))) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= k)) (PreH21 : (k <= n_pre)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_89 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((k - (Znth (i - 0 ) sorted 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k - (Znth (i - 0 ) sorted 0) )) ”
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((k - (Znth (i - 0 ) sorted 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k - (Znth (i - 0 ) sorted 0) )) ”
).

Definition solver_safety_wit_89_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((k - (Znth (i - 0 ) sorted 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_89_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((INT_MIN) <= (k - (Znth (i - 0 ) sorted 0) )) ”
.

Definition solver_safety_wit_90 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> (k - (Znth (i - 0 ) sorted 0) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((sad - ((Znth (i - 0 ) sorted 0) + 1 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sad - ((Znth (i - 0 ) sorted 0) + 1 ) )) ”
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> (k - (Znth (i - 0 ) sorted 0) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((sad - ((Znth (i - 0 ) sorted 0) + 1 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sad - ((Znth (i - 0 ) sorted 0) + 1 ) )) ”
).

Definition solver_safety_wit_90_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> (k - (Znth (i - 0 ) sorted 0) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((sad - ((Znth (i - 0 ) sorted 0) + 1 ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_90_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> (k - (Znth (i - 0 ) sorted 0) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((INT_MIN) <= (sad - ((Znth (i - 0 ) sorted 0) + 1 ) )) ”
.

Definition solver_safety_wit_91 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> (k - (Znth (i - 0 ) sorted 0) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (((Znth (i - 0 ) sorted 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (i - 0 ) sorted 0) + 1 )) ”
.

Definition solver_safety_wit_92 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> (k - (Znth (i - 0 ) sorted 0) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_93 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> (sad - ((Znth (i - 0 ) sorted 0) + 1 ) ))
  **  ((( &( "k" ) )) # Int  |-> (k - (Znth (i - 0 ) sorted 0) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_94 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (k > sad)) (PreH2 : (i >= oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> sad)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((sad - sad ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sad - sad )) ”
.

Definition solver_safety_wit_95 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (k > sad)) (PreH2 : ((Znth (i - 0 ) sorted 0) > k)) (PreH3 : (i < oc)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (allone = 0)) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : ((Zlength (sorted)) = oc)) (PreH14 : (Permutation blocks sorted )) (PreH15 : (increasing sorted )) (PreH16 : (ExamOptimizationSummary values base_sad two blocks )) (PreH17 : (OptimizationSafetyBounds base_sad two blocks )) (PreH18 : (MinValue k_pre two use )) (PreH19 : (0 <= use)) (PreH20 : (use <= k_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= oc)) (PreH23 : (0 <= sad)) (PreH24 : (sad <= n_pre)) (PreH25 : (0 <= k)) (PreH26 : (k <= n_pre)) (PreH27 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> sad)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((sad - sad ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sad - sad )) ”
.

Definition solver_safety_wit_96 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (k <= sad)) (PreH2 : (i >= oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((sad - k ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sad - k )) ”
.

Definition solver_safety_wit_97 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (k <= sad)) (PreH2 : ((Znth (i - 0 ) sorted 0) > k)) (PreH3 : (i < oc)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (allone = 0)) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : ((Zlength (sorted)) = oc)) (PreH14 : (Permutation blocks sorted )) (PreH15 : (increasing sorted )) (PreH16 : (ExamOptimizationSummary values base_sad two blocks )) (PreH17 : (OptimizationSafetyBounds base_sad two blocks )) (PreH18 : (MinValue k_pre two use )) (PreH19 : (0 <= use)) (PreH20 : (use <= k_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= oc)) (PreH23 : (0 <= sad)) (PreH24 : (sad <= n_pre)) (PreH25 : (0 <= k)) (PreH26 : (k <= n_pre)) (PreH27 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((sad - k ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sad - k )) ”
.

Definition solver_safety_wit_98 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (k > sad)) (PreH2 : (i >= oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> (sad - sad ))
  **  ((( &( "k" ) )) # Int  |-> sad)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_99 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (k > sad)) (PreH2 : ((Znth (i - 0 ) sorted 0) > k)) (PreH3 : (i < oc)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (allone = 0)) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : ((Zlength (sorted)) = oc)) (PreH14 : (Permutation blocks sorted )) (PreH15 : (increasing sorted )) (PreH16 : (ExamOptimizationSummary values base_sad two blocks )) (PreH17 : (OptimizationSafetyBounds base_sad two blocks )) (PreH18 : (MinValue k_pre two use )) (PreH19 : (0 <= use)) (PreH20 : (use <= k_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= oc)) (PreH23 : (0 <= sad)) (PreH24 : (sad <= n_pre)) (PreH25 : (0 <= k)) (PreH26 : (k <= n_pre)) (PreH27 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> (sad - sad ))
  **  ((( &( "k" ) )) # Int  |-> sad)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_100 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (k <= sad)) (PreH2 : (i >= oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> (sad - k ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_101 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (k <= sad)) (PreH2 : ((Znth (i - 0 ) sorted 0) > k)) (PreH3 : (i < oc)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (allone = 0)) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : ((Zlength (sorted)) = oc)) (PreH14 : (Permutation blocks sorted )) (PreH15 : (increasing sorted )) (PreH16 : (ExamOptimizationSummary values base_sad two blocks )) (PreH17 : (OptimizationSafetyBounds base_sad two blocks )) (PreH18 : (MinValue k_pre two use )) (PreH19 : (0 <= use)) (PreH20 : (use <= k_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= oc)) (PreH23 : (0 <= sad)) (PreH24 : (sad <= n_pre)) (PreH25 : (0 <= k)) (PreH26 : (k <= n_pre)) (PreH27 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> (sad - k ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_102 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - sad ) < 0)) (PreH2 : (k > sad)) (PreH3 : (i >= oc)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (allone = 0)) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : ((Zlength (sorted)) = oc)) (PreH14 : (Permutation blocks sorted )) (PreH15 : (increasing sorted )) (PreH16 : (ExamOptimizationSummary values base_sad two blocks )) (PreH17 : (OptimizationSafetyBounds base_sad two blocks )) (PreH18 : (MinValue k_pre two use )) (PreH19 : (0 <= use)) (PreH20 : (use <= k_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= oc)) (PreH23 : (0 <= sad)) (PreH24 : (sad <= n_pre)) (PreH25 : (0 <= k)) (PreH26 : (k <= n_pre)) (PreH27 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> (sad - sad ))
  **  ((( &( "k" ) )) # Int  |-> sad)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_103 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - sad ) < 0)) (PreH2 : (k > sad)) (PreH3 : ((Znth (i - 0 ) sorted 0) > k)) (PreH4 : (i < oc)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (allone = 0)) (PreH10 : (ones <> 0)) (PreH11 : (0 <= oc)) (PreH12 : (oc <= n_pre)) (PreH13 : ((Zlength (blocks)) = oc)) (PreH14 : ((Zlength (sorted)) = oc)) (PreH15 : (Permutation blocks sorted )) (PreH16 : (increasing sorted )) (PreH17 : (ExamOptimizationSummary values base_sad two blocks )) (PreH18 : (OptimizationSafetyBounds base_sad two blocks )) (PreH19 : (MinValue k_pre two use )) (PreH20 : (0 <= use)) (PreH21 : (use <= k_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= oc)) (PreH24 : (0 <= sad)) (PreH25 : (sad <= n_pre)) (PreH26 : (0 <= k)) (PreH27 : (k <= n_pre)) (PreH28 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> (sad - sad ))
  **  ((( &( "k" ) )) # Int  |-> sad)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_104 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - k ) < 0)) (PreH2 : (k <= sad)) (PreH3 : (i >= oc)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (allone = 0)) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : ((Zlength (sorted)) = oc)) (PreH14 : (Permutation blocks sorted )) (PreH15 : (increasing sorted )) (PreH16 : (ExamOptimizationSummary values base_sad two blocks )) (PreH17 : (OptimizationSafetyBounds base_sad two blocks )) (PreH18 : (MinValue k_pre two use )) (PreH19 : (0 <= use)) (PreH20 : (use <= k_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= oc)) (PreH23 : (0 <= sad)) (PreH24 : (sad <= n_pre)) (PreH25 : (0 <= k)) (PreH26 : (k <= n_pre)) (PreH27 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> (sad - k ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_105 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - k ) < 0)) (PreH2 : (k <= sad)) (PreH3 : ((Znth (i - 0 ) sorted 0) > k)) (PreH4 : (i < oc)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (allone = 0)) (PreH10 : (ones <> 0)) (PreH11 : (0 <= oc)) (PreH12 : (oc <= n_pre)) (PreH13 : ((Zlength (blocks)) = oc)) (PreH14 : ((Zlength (sorted)) = oc)) (PreH15 : (Permutation blocks sorted )) (PreH16 : (increasing sorted )) (PreH17 : (ExamOptimizationSummary values base_sad two blocks )) (PreH18 : (OptimizationSafetyBounds base_sad two blocks )) (PreH19 : (MinValue k_pre two use )) (PreH20 : (0 <= use)) (PreH21 : (use <= k_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= oc)) (PreH24 : (0 <= sad)) (PreH25 : (sad <= n_pre)) (PreH26 : (0 <= k)) (PreH27 : (k <= n_pre)) (PreH28 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "sad" ) )) # Int  |-> (sad - k ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ False ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH5 : (n_pre = (Zlength (values)))),
  (Int64Array.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= 1) ”
  &&  “ (1 <= 1) ”
  &&  “ (AllOnePrefix values 0 1 ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH5 : (n_pre = (Zlength (values)))),
  TT && emp 
|--
  “ (AllOnePrefix values 0 1 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH5 : (n_pre = (Zlength (values)))),
  (AllOnePrefix values 0 1 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH5 : (n_pre = (Zlength (values)))),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_2_1 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ (AllOnePrefix values (i + 1 ) 0 ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )),
  TT && emp 
|--
  “ (AllOnePrefix values (i + 1 ) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )),
  (AllOnePrefix values (i + 1 ) 0 )
.

Definition solver_entail_wit_2_2 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= allone) ”
  &&  “ (allone <= 1) ”
  &&  “ (AllOnePrefix values (i + 1 ) allone ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )),
  TT && emp 
|--
  “ (AllOnePrefix values (i + 1 ) allone ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )),
  (AllOnePrefix values (i + 1 ) allone )
.

Definition solver_entail_wit_3 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= allone)) (PreH10 : (allone <= 1)) (PreH11 : (AllOnePrefix values i allone )) (PreH12 : (allone = 0)),
  (Int64Array.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (0 = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (CoprimeEdgePrefixCount values 0 0 ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= allone)) (PreH10 : (allone <= 1)) (PreH11 : (AllOnePrefix values i allone )) (PreH12 : (allone = 0)),
  TT && emp 
|--
  “ (CoprimeEdgePrefixCount values 0 0 ) ”
  &&  “ (AllOnePrefix values n_pre 0 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= allone)) (PreH10 : (allone <= 1)) (PreH11 : (AllOnePrefix values i allone )) (PreH12 : (allone = 0)),
  (CoprimeEdgePrefixCount values 0 0 )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= allone)) (PreH10 : (allone <= 1)) (PreH11 : (AllOnePrefix values i allone )) (PreH12 : (allone = 0)),
  (AllOnePrefix values n_pre 0 )
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= allone)) (PreH10 : (allone <= 1)) (PreH11 : (AllOnePrefix values i allone )) (PreH12 : (allone = 0)),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_4_1 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (two = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (0 <= sad)) (PreH15 : (sad <= i)) (PreH16 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (two = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ (0 <= (sad + 1 )) ”
  &&  “ ((sad + 1 ) <= (i + 1 )) ”
  &&  “ (CoprimeEdgePrefixCount values (i + 1 ) (sad + 1 ) ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (two = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (0 <= sad)) (PreH15 : (sad <= i)) (PreH16 : (CoprimeEdgePrefixCount values i sad )),
  TT && emp 
|--
  “ (CoprimeEdgePrefixCount values (i + 1 ) (sad + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (two = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (0 <= sad)) (PreH15 : (sad <= i)) (PreH16 : (CoprimeEdgePrefixCount values i sad )),
  (CoprimeEdgePrefixCount values (i + 1 ) (sad + 1 ) )
.

Definition solver_entail_wit_4_2 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (two = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (0 <= sad)) (PreH15 : (sad <= i)) (PreH16 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (two = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad <= (i + 1 )) ”
  &&  “ (CoprimeEdgePrefixCount values (i + 1 ) sad ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (two = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (0 <= sad)) (PreH15 : (sad <= i)) (PreH16 : (CoprimeEdgePrefixCount values i sad )),
  TT && emp 
|--
  “ (CoprimeEdgePrefixCount values (i + 1 ) sad ) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (two = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (0 <= sad)) (PreH15 : (sad <= i)) (PreH16 : (CoprimeEdgePrefixCount values i sad )),
  (CoprimeEdgePrefixCount values (i + 1 ) sad )
.

Definition solver_entail_wit_5 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i_4: Z) (two: Z) (allone: Z) (PreH1 : ((i_4 + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (two = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (0 <= i_4)) (PreH11 : (i_4 <= (n_pre - 1 ))) (PreH12 : (0 <= sad)) (PreH13 : (sad <= i_4)) (PreH14 : (CoprimeEdgePrefixCount values i_4 sad )),
  ((( &( "i" ) )) # Int  |-> 0)
  **  (Int64Array.full a_pre n_pre values )
|--
  (EX (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i) ”
  &&  “ ((Znth (i - 1 ) values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i_2) ”
  &&  “ ((Znth i_2 values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i_2 two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (“ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i_3) ”
  &&  “ (i_3 = 0) ”
  &&  “ (PairSavingsPrefix values i_3 two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values ))
.

Definition solver_entail_wit_6_1 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : ((Znth (i - 1 ) values 0) = 1)) (PreH18 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
|--
  EX (scan_savings: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ (PairRunSuffix values (i + 1 ) 0 ) ”
  &&  “ (scan_savings = (two + (0 ÷ 2 ) )) ”
  &&  “ (PairSavingsScan values (i + 1 ) two 0 scan_savings ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : ((Znth (i - 1 ) values 0) = 1)) (PreH18 : (PairSavingsPrefix values i two )),
  TT && emp 
|--
  “ (PairSavingsScan values (i + 1 ) two 0 (two + (0 ÷ 2 ) ) ) ”
  &&  “ (PairRunSuffix values (i + 1 ) 0 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_6_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : ((Znth (i - 1 ) values 0) = 1)) (PreH18 : (PairSavingsPrefix values i two )),
  (PairSavingsScan values (i + 1 ) two 0 (two + (0 ÷ 2 ) ) )
.

Definition solver_entail_wit_6_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : ((Znth (i - 1 ) values 0) = 1)) (PreH18 : (PairSavingsPrefix values i two )),
  (PairRunSuffix values (i + 1 ) 0 )
.

Definition solver_entail_wit_6_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : ((Znth (i - 1 ) values 0) = 1)) (PreH18 : (PairSavingsPrefix values i two )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_6_2 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : (i = 0)) (PreH18 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
|--
  EX (scan_savings: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ (PairRunSuffix values (i + 1 ) 0 ) ”
  &&  “ (scan_savings = (two + (0 ÷ 2 ) )) ”
  &&  “ (PairSavingsScan values (i + 1 ) two 0 scan_savings ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : (i = 0)) (PreH18 : (PairSavingsPrefix values i two )),
  TT && emp 
|--
  “ (PairSavingsScan values (0 + 1 ) two 0 (two + (0 ÷ 2 ) ) ) ”
  &&  “ (PairRunSuffix values (0 + 1 ) 0 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_6_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : (i = 0)) (PreH18 : (PairSavingsPrefix values i two )),
  (PairSavingsScan values (0 + 1 ) two 0 (two + (0 ÷ 2 ) ) )
.

Definition solver_entail_wit_6_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : (i = 0)) (PreH18 : (PairSavingsPrefix values i two )),
  (PairRunSuffix values (0 + 1 ) 0 )
.

Definition solver_entail_wit_6_2_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i)) (PreH17 : (i = 0)) (PreH18 : (PairSavingsPrefix values i two )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_7_1 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings_2: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings_2 = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings_2 )),
  (Int64Array.full a_pre n_pre values )
|--
  EX (scan_savings: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ (0 <= (run + 1 )) ”
  &&  “ ((run + 1 ) <= ((i + 1 ) + 1 )) ”
  &&  “ (PairRunSuffix values ((i + 1 ) + 1 ) (run + 1 ) ) ”
  &&  “ (scan_savings = (two + ((run + 1 ) ÷ 2 ) )) ”
  &&  “ (PairSavingsScan values ((i + 1 ) + 1 ) two (run + 1 ) scan_savings ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (scan_savings_2: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings_2 = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings_2 )),
  TT && emp 
|--
  “ (PairSavingsScan values ((i + 1 ) + 1 ) two (run + 1 ) (two + ((run + 1 ) ÷ 2 ) ) ) ”
  &&  “ (PairRunSuffix values ((i + 1 ) + 1 ) (run + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (scan_savings_2: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings_2 = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings_2 )),
  (PairSavingsScan values ((i + 1 ) + 1 ) two (run + 1 ) (two + ((run + 1 ) ÷ 2 ) ) )
.

Definition solver_entail_wit_7_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (scan_savings_2: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings_2 = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings_2 )),
  (PairRunSuffix values ((i + 1 ) + 1 ) (run + 1 ) )
.

Definition solver_entail_wit_7_2 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings_2: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings_2 = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings_2 )),
  (Int64Array.full a_pre n_pre values )
|--
  EX (scan_savings: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (0 <= (two + (run ÷ 2 ) )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((i + 1 ) + 1 )) ”
  &&  “ (PairRunSuffix values ((i + 1 ) + 1 ) 0 ) ”
  &&  “ (scan_savings = ((two + (run ÷ 2 ) ) + (0 ÷ 2 ) )) ”
  &&  “ (PairSavingsScan values ((i + 1 ) + 1 ) (two + (run ÷ 2 ) ) 0 scan_savings ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (scan_savings_2: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings_2 = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings_2 )),
  TT && emp 
|--
  “ (PairSavingsScan values ((i + 1 ) + 1 ) (two + (run ÷ 2 ) ) 0 ((two + (run ÷ 2 ) ) + (0 ÷ 2 ) ) ) ”
  &&  “ (PairRunSuffix values ((i + 1 ) + 1 ) 0 ) ”
  &&  “ (0 <= (two + (run ÷ 2 ) )) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (scan_savings_2: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings_2 = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings_2 )),
  (PairSavingsScan values ((i + 1 ) + 1 ) (two + (run ÷ 2 ) ) 0 ((two + (run ÷ 2 ) ) + (0 ÷ 2 ) ) )
.

Definition solver_entail_wit_7_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (scan_savings_2: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings_2 = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings_2 )),
  (PairRunSuffix values ((i + 1 ) + 1 ) 0 )
.

Definition solver_entail_wit_7_2_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (scan_savings_2: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (GcdResult (Znth i values 0) (Znth (i + 1 ) values 0) retval )) (PreH3 : ((Znth (i + 1 ) values 0) <> 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (0 <= sad)) (PreH14 : (sad < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= two)) (PreH18 : (0 <= run)) (PreH19 : (run <= (i + 1 ))) (PreH20 : (PairRunSuffix values (i + 1 ) run )) (PreH21 : (scan_savings_2 = (two + (run ÷ 2 ) ))) (PreH22 : (PairSavingsScan values (i + 1 ) two run scan_savings_2 )),
  (0 <= (two + (run ÷ 2 ) ))
.

Definition solver_entail_wit_8_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i_4: Z) (sad: Z) (allone: Z) (PreH1 : ((i_4 + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i_4)) (PreH13 : (i_4 < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i_4 + 1 ))) (PreH17 : (PairRunSuffix values (i_4 + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i_4 + 1 ) two run scan_savings )),
  ((( &( "i" ) )) # Int  |-> (i_4 + 1 ))
  **  (Int64Array.full a_pre n_pre values )
|--
  (EX (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= (two + (run ÷ 2 ) )) ”
  &&  “ ((2 * (two + (run ÷ 2 ) ) ) <= i) ”
  &&  “ ((Znth (i - 1 ) values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i (two + (run ÷ 2 ) ) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= (two + (run ÷ 2 ) )) ”
  &&  “ ((2 * (two + (run ÷ 2 ) ) ) <= i_2) ”
  &&  “ ((Znth i_2 values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i_2 (two + (run ÷ 2 ) ) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (“ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= (two + (run ÷ 2 ) )) ”
  &&  “ ((2 * (two + (run ÷ 2 ) ) ) <= n_pre) ”
  &&  “ (PairSavingsPrefix values n_pre (two + (run ÷ 2 ) ) ) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= (two + (run ÷ 2 ) )) ”
  &&  “ ((2 * (two + (run ÷ 2 ) ) ) <= i_3) ”
  &&  “ (i_3 = 0) ”
  &&  “ (PairSavingsPrefix values i_3 (two + (run ÷ 2 ) ) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values ))
.

Definition solver_entail_wit_8_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i_4: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i_4 + 1 ) values 0) = 1)) (PreH2 : ((i_4 + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i_4)) (PreH14 : (i_4 < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i_4 + 1 ))) (PreH18 : (PairRunSuffix values (i_4 + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i_4 + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "i" ) )) # Int  |-> (i_4 + 1 ))
|--
  (EX (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= (two + (run ÷ 2 ) )) ”
  &&  “ ((2 * (two + (run ÷ 2 ) ) ) <= i) ”
  &&  “ ((Znth (i - 1 ) values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i (two + (run ÷ 2 ) ) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= (two + (run ÷ 2 ) )) ”
  &&  “ ((2 * (two + (run ÷ 2 ) ) ) <= i_2) ”
  &&  “ ((Znth i_2 values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i_2 (two + (run ÷ 2 ) ) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (“ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= (two + (run ÷ 2 ) )) ”
  &&  “ ((2 * (two + (run ÷ 2 ) ) ) <= n_pre) ”
  &&  “ (PairSavingsPrefix values n_pre (two + (run ÷ 2 ) ) ) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= (two + (run ÷ 2 ) )) ”
  &&  “ ((2 * (two + (run ÷ 2 ) ) ) <= i_3) ”
  &&  “ (i_3 = 0) ”
  &&  “ (PairSavingsPrefix values i_3 (two + (run ÷ 2 ) ) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values ))
.

Definition solver_entail_wit_8_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i_4: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i_4 values 0) = 1)) (PreH2 : (i_4 < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i_4)) (PreH14 : (i_4 <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i_4)) (PreH17 : ((Znth (i_4 - 1 ) values 0) = 1)) (PreH18 : (PairSavingsPrefix values i_4 two )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "i" ) )) # Int  |-> (i_4 + 1 ))
|--
  (EX (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i) ”
  &&  “ ((Znth (i - 1 ) values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i_2) ”
  &&  “ ((Znth i_2 values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i_2 two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (“ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i_3) ”
  &&  “ (i_3 = 0) ”
  &&  “ (PairSavingsPrefix values i_3 two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values ))
.

Definition solver_entail_wit_8_4 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i_4: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i_4 values 0) = 1)) (PreH2 : (i_4 < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i_4)) (PreH14 : (i_4 <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i_4)) (PreH17 : ((Znth i_4 values 0) = 1)) (PreH18 : (PairSavingsPrefix values i_4 two )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "i" ) )) # Int  |-> (i_4 + 1 ))
|--
  (EX (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i) ”
  &&  “ ((Znth (i - 1 ) values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i_2) ”
  &&  “ ((Znth i_2 values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i_2 two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (“ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i_3) ”
  &&  “ (i_3 = 0) ”
  &&  “ (PairSavingsPrefix values i_3 two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values ))
.

Definition solver_entail_wit_8_5 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i_4: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth i_4 values 0) = 1)) (PreH2 : (i_4 < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i_4)) (PreH14 : (i_4 <= n_pre)) (PreH15 : (0 <= two)) (PreH16 : ((2 * two ) <= i_4)) (PreH17 : (i_4 = 0)) (PreH18 : (PairSavingsPrefix values i_4 two )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "i" ) )) # Int  |-> (i_4 + 1 ))
|--
  (EX (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i) ”
  &&  “ ((Znth (i - 1 ) values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i_2) ”
  &&  “ ((Znth i_2 values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i_2 two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (“ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values ))
  ||
  (EX (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i_3) ”
  &&  “ (i_3 = 0) ”
  &&  “ (PairSavingsPrefix values i_3 two ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values ))
.

Definition solver_entail_wit_9_1 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth (i - 1 ) values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth (i - 1 ) values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  TT && emp 
|--
  “ (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_9_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth (i - 1 ) values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) )
.

Definition solver_entail_wit_9_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth (i - 1 ) values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  (PairSavingsPrefix values n_pre two )
.

Definition solver_entail_wit_9_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth (i - 1 ) values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_9_2 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth i values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth i values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  TT && emp 
|--
  “ (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_9_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth i values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) )
.

Definition solver_entail_wit_9_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth i values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  (PairSavingsPrefix values n_pre two )
.

Definition solver_entail_wit_9_2_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth i values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_9_3 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (allone: Z) (PreH1 : (n_pre >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= n_pre)) (PreH16 : (PairSavingsPrefix values n_pre two )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (allone: Z) (PreH1 : (n_pre >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= n_pre)) (PreH16 : (PairSavingsPrefix values n_pre two )),
  TT && emp 
|--
  “ (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_9_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (allone: Z) (PreH1 : (n_pre >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= n_pre)) (PreH16 : (PairSavingsPrefix values n_pre two )),
  (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) )
.

Definition solver_entail_wit_9_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (allone: Z) (PreH1 : (n_pre >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= n_pre)) (PreH16 : (PairSavingsPrefix values n_pre two )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_10 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (sad: Z) (two: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (PairSavingsPrefix values n_pre two )) (PreH11 : (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) )) (PreH12 : (0 <= sad)) (PreH13 : (sad < n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= n_pre)),
  ((( &( "i" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval n_pre )
  **  (Int64Array.full a_pre n_pre values )
|--
  (EX (blocks: (@list Z)) (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (retval <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= i) ”
  &&  “ ((Zlength (blocks)) = 0) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg retval 0 0 blocks )
  **  (IntArray.undef_seg retval 0 n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (retval <> 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ ((Zlength (blocks)) = 0) ”
  &&  “ ((Znth i_2 values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_2 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_2 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg retval 0 0 blocks )
  **  (IntArray.undef_seg retval 0 n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (retval <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (blocks)) = 0) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg retval 0 0 blocks )
  **  (IntArray.undef_seg retval 0 n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (retval <> 0) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= i_3) ”
  &&  “ ((Zlength (blocks)) = 0) ”
  &&  “ (i_3 = 0) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_3 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_3 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg retval 0 0 blocks )
  **  (IntArray.undef_seg retval 0 n_pre ))
.

Definition solver_entail_wit_11_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= i)) (PreH15 : ((Zlength (blocks_2)) = oc)) (PreH16 : ((Znth (i - 1 ) values 0) <> 1)) (PreH17 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH18 : (PairSavingsPrefix values n_pre two )) (PreH19 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH20 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH21 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH22 : (0 <= sad)) (PreH23 : (sad < n_pre)) (PreH24 : (0 <= two)) (PreH25 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (i = 0) ”
  &&  “ ((Znth i values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values i i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ ((Znth i values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values i i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_11_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= i)) (PreH15 : ((Zlength (blocks_2)) = oc)) (PreH16 : (i = 0)) (PreH17 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH18 : (PairSavingsPrefix values n_pre two )) (PreH19 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH20 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH21 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH22 : (0 <= sad)) (PreH23 : (sad < n_pre)) (PreH24 : (0 <= two)) (PreH25 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (i = 0) ”
  &&  “ ((Znth i values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values i i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ ((Znth i values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values i i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_12_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= l)) (PreH12 : (l <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= oc)) (PreH15 : (oc <= l)) (PreH16 : ((Zlength (blocks_2)) = oc)) (PreH17 : (l = 0)) (PreH18 : ((Znth l values 0) = 1)) (PreH19 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH20 : (PairSavingsPrefix values n_pre two )) (PreH21 : (CanonicalOneRunScanState values l i blocks_2 )) (PreH22 : (JointPairBlockPrefix values l sad two blocks_2 )) (PreH23 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= l) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (l = 0) ”
  &&  “ ((Znth l values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values l (i + 1 ) blocks ) ”
  &&  “ (JointPairBlockPrefix values l sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= l) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (l - 1 ) values 0) <> 1) ”
  &&  “ ((Znth l values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values l (i + 1 ) blocks ) ”
  &&  “ (JointPairBlockPrefix values l sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_12_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= l)) (PreH12 : (l <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= oc)) (PreH15 : (oc <= l)) (PreH16 : ((Zlength (blocks_2)) = oc)) (PreH17 : ((Znth (l - 1 ) values 0) <> 1)) (PreH18 : ((Znth l values 0) = 1)) (PreH19 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH20 : (PairSavingsPrefix values n_pre two )) (PreH21 : (CanonicalOneRunScanState values l i blocks_2 )) (PreH22 : (JointPairBlockPrefix values l sad two blocks_2 )) (PreH23 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= l) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (l = 0) ”
  &&  “ ((Znth l values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values l (i + 1 ) blocks ) ”
  &&  “ (JointPairBlockPrefix values l sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= l) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (l - 1 ) values 0) <> 1) ”
  &&  “ ((Znth l values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values l (i + 1 ) blocks ) ”
  &&  “ (JointPairBlockPrefix values l sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_13_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i_4: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i_4 < n_pre)) (PreH2 : (l > 0)) (PreH3 : ((Znth i_4 values 0) <> 1)) (PreH4 : (i_4 < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (ones <> 0)) (PreH13 : (0 <= l)) (PreH14 : (l <= i_4)) (PreH15 : (i_4 <= n_pre)) (PreH16 : (0 <= oc)) (PreH17 : (oc <= l)) (PreH18 : ((Zlength (blocks_2)) = oc)) (PreH19 : ((Znth (l - 1 ) values 0) <> 1)) (PreH20 : ((Znth l values 0) = 1)) (PreH21 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH22 : (PairSavingsPrefix values n_pre two )) (PreH23 : (CanonicalOneRunScanState values l i_4 blocks_2 )) (PreH24 : (JointPairBlockPrefix values l sad two blocks_2 )) (PreH25 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH26 : (0 <= sad)) (PreH27 : (sad < n_pre)) (PreH28 : (0 <= two)) (PreH29 : ((2 * two ) <= n_pre)),
  (IntArray.seg ones 0 (oc + 1 ) (app (blocks_2) ((cons ((i_4 - l )) ((@nil Z))))) )
  **  (IntArray.undef_seg ones (oc + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "i" ) )) # Int  |-> i_4)
|--
  (EX (blocks: (@list Z)) (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= (oc + 1 )) ”
  &&  “ ((oc + 1 ) <= i) ”
  &&  “ ((Zlength (blocks)) = (oc + 1 )) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 (oc + 1 ) blocks )
  **  (IntArray.undef_seg ones (oc + 1 ) n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= (oc + 1 )) ”
  &&  “ ((oc + 1 ) <= i_2) ”
  &&  “ ((Zlength (blocks)) = (oc + 1 )) ”
  &&  “ ((Znth i_2 values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_2 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_2 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 (oc + 1 ) blocks )
  **  (IntArray.undef_seg ones (oc + 1 ) n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= (oc + 1 )) ”
  &&  “ ((oc + 1 ) <= n_pre) ”
  &&  “ ((Zlength (blocks)) = (oc + 1 )) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 (oc + 1 ) blocks )
  **  (IntArray.undef_seg ones (oc + 1 ) n_pre ))
.

Definition solver_entail_wit_13_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i_4: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (l <= 0)) (PreH2 : ((Znth i_4 values 0) <> 1)) (PreH3 : (i_4 < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (AllOnePrefix values n_pre allone )) (PreH11 : (ones <> 0)) (PreH12 : (0 <= l)) (PreH13 : (l <= i_4)) (PreH14 : (i_4 <= n_pre)) (PreH15 : (0 <= oc)) (PreH16 : (oc <= l)) (PreH17 : ((Zlength (blocks_2)) = oc)) (PreH18 : ((Znth (l - 1 ) values 0) <> 1)) (PreH19 : ((Znth l values 0) = 1)) (PreH20 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH21 : (PairSavingsPrefix values n_pre two )) (PreH22 : (CanonicalOneRunScanState values l i_4 blocks_2 )) (PreH23 : (JointPairBlockPrefix values l sad two blocks_2 )) (PreH24 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH25 : (0 <= sad)) (PreH26 : (sad < n_pre)) (PreH27 : (0 <= two)) (PreH28 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "i" ) )) # Int  |-> i_4)
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)) (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_2) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth i_2 values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_2 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_2 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_3) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (i_3 = 0) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_3 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_3 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_13_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i_4: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (l <= 0)) (PreH2 : ((Znth i_4 values 0) <> 1)) (PreH3 : (i_4 < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (AllOnePrefix values n_pre allone )) (PreH11 : (ones <> 0)) (PreH12 : (0 <= l)) (PreH13 : (l <= i_4)) (PreH14 : (i_4 <= n_pre)) (PreH15 : (0 <= oc)) (PreH16 : (oc <= l)) (PreH17 : ((Zlength (blocks_2)) = oc)) (PreH18 : (l = 0)) (PreH19 : ((Znth l values 0) = 1)) (PreH20 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH21 : (PairSavingsPrefix values n_pre two )) (PreH22 : (CanonicalOneRunScanState values l i_4 blocks_2 )) (PreH23 : (JointPairBlockPrefix values l sad two blocks_2 )) (PreH24 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH25 : (0 <= sad)) (PreH26 : (sad < n_pre)) (PreH27 : (0 <= two)) (PreH28 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "i" ) )) # Int  |-> i_4)
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)) (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_2) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth i_2 values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_2 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_2 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_13_4 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i_4: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (l <= 0)) (PreH2 : (i_4 >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= l)) (PreH12 : (l <= i_4)) (PreH13 : (i_4 <= n_pre)) (PreH14 : (0 <= oc)) (PreH15 : (oc <= l)) (PreH16 : ((Zlength (blocks_2)) = oc)) (PreH17 : (l = 0)) (PreH18 : ((Znth l values 0) = 1)) (PreH19 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH20 : (PairSavingsPrefix values n_pre two )) (PreH21 : (CanonicalOneRunScanState values l i_4 blocks_2 )) (PreH22 : (JointPairBlockPrefix values l sad two blocks_2 )) (PreH23 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  ((( &( "i" ) )) # Int  |-> i_4)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)) (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_2) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth i_2 values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_2 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_2 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_3) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (i_3 = 0) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_3 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_3 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_13_5 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i_4: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (l <= 0)) (PreH2 : (i_4 >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= l)) (PreH12 : (l <= i_4)) (PreH13 : (i_4 <= n_pre)) (PreH14 : (0 <= oc)) (PreH15 : (oc <= l)) (PreH16 : ((Zlength (blocks_2)) = oc)) (PreH17 : ((Znth (l - 1 ) values 0) <> 1)) (PreH18 : ((Znth l values 0) = 1)) (PreH19 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH20 : (PairSavingsPrefix values n_pre two )) (PreH21 : (CanonicalOneRunScanState values l i_4 blocks_2 )) (PreH22 : (JointPairBlockPrefix values l sad two blocks_2 )) (PreH23 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  ((( &( "i" ) )) # Int  |-> i_4)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)) (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_2) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth i_2 values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_2 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_2 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_3) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (i_3 = 0) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_3 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_3 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_13_6 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i_4: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i_4 >= n_pre)) (PreH2 : (l > 0)) (PreH3 : (i_4 >= n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH9 : (allone = 0)) (PreH10 : (AllOnePrefix values n_pre allone )) (PreH11 : (ones <> 0)) (PreH12 : (0 <= l)) (PreH13 : (l <= i_4)) (PreH14 : (i_4 <= n_pre)) (PreH15 : (0 <= oc)) (PreH16 : (oc <= l)) (PreH17 : ((Zlength (blocks_2)) = oc)) (PreH18 : ((Znth (l - 1 ) values 0) <> 1)) (PreH19 : ((Znth l values 0) = 1)) (PreH20 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH21 : (PairSavingsPrefix values n_pre two )) (PreH22 : (CanonicalOneRunScanState values l i_4 blocks_2 )) (PreH23 : (JointPairBlockPrefix values l sad two blocks_2 )) (PreH24 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH25 : (0 <= sad)) (PreH26 : (sad < n_pre)) (PreH27 : (0 <= two)) (PreH28 : ((2 * two ) <= n_pre)),
  ((( &( "i" ) )) # Int  |-> i_4)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)) (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_2) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth i_2 values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_2 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_2 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_3) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (i_3 = 0) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_3 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_3 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_13_7 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i_4: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i_4 values 0) <> 1)) (PreH2 : (i_4 < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= i_4)) (PreH12 : (i_4 <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= i_4)) (PreH15 : ((Zlength (blocks_2)) = oc)) (PreH16 : ((Znth (i_4 - 1 ) values 0) <> 1)) (PreH17 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH18 : (PairSavingsPrefix values n_pre two )) (PreH19 : (CanonicalInteriorOneRunPrefix values i_4 blocks_2 )) (PreH20 : (JointPairBlockPrefix values i_4 sad two blocks_2 )) (PreH21 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH22 : (0 <= sad)) (PreH23 : (sad < n_pre)) (PreH24 : (0 <= two)) (PreH25 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "i" ) )) # Int  |-> (i_4 + 1 ))
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)) (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_2) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth i_2 values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_2 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_2 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_3) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (i_3 = 0) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_3 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_3 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_13_8 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i_4: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i_4 values 0) <> 1)) (PreH2 : (i_4 < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= i_4)) (PreH12 : (i_4 <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= i_4)) (PreH15 : ((Zlength (blocks_2)) = oc)) (PreH16 : ((Znth i_4 values 0) <> 1)) (PreH17 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH18 : (PairSavingsPrefix values n_pre two )) (PreH19 : (CanonicalInteriorOneRunPrefix values i_4 blocks_2 )) (PreH20 : (JointPairBlockPrefix values i_4 sad two blocks_2 )) (PreH21 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH22 : (0 <= sad)) (PreH23 : (sad < n_pre)) (PreH24 : (0 <= two)) (PreH25 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "i" ) )) # Int  |-> (i_4 + 1 ))
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)) (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_2) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth i_2 values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_2 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_2 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_3) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (i_3 = 0) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_3 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_3 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_13_9 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i_4: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth i_4 values 0) <> 1)) (PreH2 : (i_4 < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (ones <> 0)) (PreH11 : (0 <= i_4)) (PreH12 : (i_4 <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= i_4)) (PreH15 : ((Zlength (blocks_2)) = oc)) (PreH16 : (i_4 = 0)) (PreH17 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH18 : (PairSavingsPrefix values n_pre two )) (PreH19 : (CanonicalInteriorOneRunPrefix values i_4 blocks_2 )) (PreH20 : (JointPairBlockPrefix values i_4 sad two blocks_2 )) (PreH21 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH22 : (0 <= sad)) (PreH23 : (sad < n_pre)) (PreH24 : (0 <= two)) (PreH25 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "i" ) )) # Int  |-> (i_4 + 1 ))
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  (EX (blocks: (@list Z)) (i: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_2: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_2) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth i_2 values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_2 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_2 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
  ||
  (EX (blocks: (@list Z)) (i_3: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i_3) ”
  &&  “ (i_3 <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i_3) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (i_3 = 0) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i_3 blocks ) ”
  &&  “ (JointPairBlockPrefix values i_3 sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i_3)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre ))
.

Definition solver_entail_wit_14_1 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth (i - 1 ) values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (ExamJointOptimizationCertificate values sad two blocks ) ”
  &&  “ (ExamOptimizationSummary values sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth (i - 1 ) values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  TT && emp 
|--
  “ (OptimizationSafetyBounds sad two blocks_2 ) ”
  &&  “ (ExamOptimizationSummary values sad two blocks_2 ) ”
  &&  “ (ExamJointOptimizationCertificate values sad two blocks_2 ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks_2 ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks_2 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_14_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth (i - 1 ) values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (OptimizationSafetyBounds sad two blocks_2 )
.

Definition solver_entail_wit_14_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth (i - 1 ) values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (ExamOptimizationSummary values sad two blocks_2 )
.

Definition solver_entail_wit_14_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth (i - 1 ) values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (ExamJointOptimizationCertificate values sad two blocks_2 )
.

Definition solver_entail_wit_14_1_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth (i - 1 ) values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (JointPairBlockPrefix values n_pre sad two blocks_2 )
.

Definition solver_entail_wit_14_1_split_goal_5 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth (i - 1 ) values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )
.

Definition solver_entail_wit_14_1_split_goal_6 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth (i - 1 ) values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_14_2 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth i values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (ExamJointOptimizationCertificate values sad two blocks ) ”
  &&  “ (ExamOptimizationSummary values sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth i values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  TT && emp 
|--
  “ (OptimizationSafetyBounds sad two blocks_2 ) ”
  &&  “ (ExamOptimizationSummary values sad two blocks_2 ) ”
  &&  “ (ExamJointOptimizationCertificate values sad two blocks_2 ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks_2 ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks_2 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_14_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth i values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (OptimizationSafetyBounds sad two blocks_2 )
.

Definition solver_entail_wit_14_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth i values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (ExamOptimizationSummary values sad two blocks_2 )
.

Definition solver_entail_wit_14_2_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth i values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (ExamJointOptimizationCertificate values sad two blocks_2 )
.

Definition solver_entail_wit_14_2_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth i values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (JointPairBlockPrefix values n_pre sad two blocks_2 )
.

Definition solver_entail_wit_14_2_split_goal_5 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth i values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )
.

Definition solver_entail_wit_14_2_split_goal_6 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : ((Znth i values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks_2 )) (PreH19 : (JointPairBlockPrefix values i sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_14_3 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (n_pre >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= n_pre)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH16 : (PairSavingsPrefix values n_pre two )) (PreH17 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH18 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH19 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH20 : (0 <= sad)) (PreH21 : (sad < n_pre)) (PreH22 : (0 <= two)) (PreH23 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (ExamJointOptimizationCertificate values sad two blocks ) ”
  &&  “ (ExamOptimizationSummary values sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (n_pre >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= n_pre)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH16 : (PairSavingsPrefix values n_pre two )) (PreH17 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH18 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH19 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH20 : (0 <= sad)) (PreH21 : (sad < n_pre)) (PreH22 : (0 <= two)) (PreH23 : ((2 * two ) <= n_pre)),
  TT && emp 
|--
  “ (OptimizationSafetyBounds sad two blocks_2 ) ”
  &&  “ (ExamOptimizationSummary values sad two blocks_2 ) ”
  &&  “ (ExamJointOptimizationCertificate values sad two blocks_2 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_14_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (n_pre >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= n_pre)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH16 : (PairSavingsPrefix values n_pre two )) (PreH17 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH18 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH19 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH20 : (0 <= sad)) (PreH21 : (sad < n_pre)) (PreH22 : (0 <= two)) (PreH23 : ((2 * two ) <= n_pre)),
  (OptimizationSafetyBounds sad two blocks_2 )
.

Definition solver_entail_wit_14_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (n_pre >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= n_pre)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH16 : (PairSavingsPrefix values n_pre two )) (PreH17 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH18 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH19 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH20 : (0 <= sad)) (PreH21 : (sad < n_pre)) (PreH22 : (0 <= two)) (PreH23 : ((2 * two ) <= n_pre)),
  (ExamOptimizationSummary values sad two blocks_2 )
.

Definition solver_entail_wit_14_3_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (n_pre >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= n_pre)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH16 : (PairSavingsPrefix values n_pre two )) (PreH17 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH18 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH19 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH20 : (0 <= sad)) (PreH21 : (sad < n_pre)) (PreH22 : (0 <= two)) (PreH23 : ((2 * two ) <= n_pre)),
  (ExamJointOptimizationCertificate values sad two blocks_2 )
.

Definition solver_entail_wit_14_3_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (two: Z) (sad: Z) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (n_pre >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= n_pre)) (PreH14 : ((Zlength (blocks_2)) = oc)) (PreH15 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH16 : (PairSavingsPrefix values n_pre two )) (PreH17 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH18 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH19 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH20 : (0 <= sad)) (PreH21 : (sad < n_pre)) (PreH22 : (0 <= two)) (PreH23 : ((2 * two ) <= n_pre)),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_15 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks_2: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH6 : (allone = 0)) (PreH7 : (AllOnePrefix values n_pre allone )) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks_2)) = oc)) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (PairSavingsPrefix values n_pre two )) (PreH14 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH15 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH16 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH17 : (ExamJointOptimizationCertificate values sad two blocks_2 )) (PreH18 : (ExamOptimizationSummary values sad two blocks_2 )) (PreH19 : (OptimizationSafetyBounds sad two blocks_2 )) (PreH20 : (0 <= sad)) (PreH21 : (sad < n_pre)) (PreH22 : (0 <= two)) (PreH23 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (ExamJointOptimizationCertificate values sad two blocks ) ”
  &&  “ (ExamOptimizationSummary values sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (blocks_2: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH6 : (allone = 0)) (PreH7 : (AllOnePrefix values n_pre allone )) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks_2)) = oc)) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (PairSavingsPrefix values n_pre two )) (PreH14 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH15 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH16 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH17 : (ExamJointOptimizationCertificate values sad two blocks_2 )) (PreH18 : (ExamOptimizationSummary values sad two blocks_2 )) (PreH19 : (OptimizationSafetyBounds sad two blocks_2 )) (PreH20 : (0 <= sad)) (PreH21 : (sad < n_pre)) (PreH22 : (0 <= two)) (PreH23 : ((2 * two ) <= n_pre)),
  TT && emp 
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_15_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (blocks_2: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH6 : (allone = 0)) (PreH7 : (AllOnePrefix values n_pre allone )) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks_2)) = oc)) (PreH12 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH13 : (PairSavingsPrefix values n_pre two )) (PreH14 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH15 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH16 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH17 : (ExamJointOptimizationCertificate values sad two blocks_2 )) (PreH18 : (ExamOptimizationSummary values sad two blocks_2 )) (PreH19 : (OptimizationSafetyBounds sad two blocks_2 )) (PreH20 : (0 <= sad)) (PreH21 : (sad < n_pre)) (PreH22 : (0 <= two)) (PreH23 : ((2 * two ) <= n_pre)),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_16_1 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks_2: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (sorted_2: (@list Z)) (PreH1 : (Permutation blocks_2 sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = oc)) (PreH4 : (k_pre < two)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (ones <> 0)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= n_pre)) (PreH15 : ((Zlength (blocks_2)) = oc)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH19 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (ExamJointOptimizationCertificate values sad two blocks_2 )) (PreH22 : (ExamOptimizationSummary values sad two blocks_2 )) (PreH23 : (OptimizationSafetyBounds sad two blocks_2 )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  (IntArray.seg ones 0 oc sorted_2 )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (sorted: (@list Z)) (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (allone = 0) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values ((sad - (2 * k_pre ) ) + (2 * k_pre ) ) two blocks ) ”
  &&  “ (OptimizationSafetyBounds ((sad - (2 * k_pre ) ) + (2 * k_pre ) ) two blocks ) ”
  &&  “ (MinValue k_pre two k_pre ) ”
  &&  “ ((k_pre - k_pre ) = (k_pre - k_pre )) ”
  &&  “ ((sad - (2 * k_pre ) ) = (((sad - (2 * k_pre ) ) + (2 * k_pre ) ) - (2 * k_pre ) )) ”
  &&  “ (0 <= k_pre) ”
  &&  “ (k_pre <= k_pre) ”
  &&  “ (0 <= (k_pre - k_pre )) ”
  &&  “ ((k_pre - k_pre ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (blocks_2: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (sorted_2: (@list Z)) (PreH1 : (Permutation blocks_2 sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = oc)) (PreH4 : (k_pre < two)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (ones <> 0)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= n_pre)) (PreH15 : ((Zlength (blocks_2)) = oc)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH19 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (ExamJointOptimizationCertificate values sad two blocks_2 )) (PreH22 : (ExamOptimizationSummary values sad two blocks_2 )) (PreH23 : (OptimizationSafetyBounds sad two blocks_2 )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  TT && emp 
|--
  EX (blocks: (@list Z)),
  “ ((Zlength (blocks)) = (Zlength (sorted_2))) ”
  &&  “ (Permutation blocks sorted_2 ) ”
  &&  “ (ExamOptimizationSummary values ((sad - (2 * k_pre ) ) + (2 * k_pre ) ) two blocks ) ”
  &&  “ (OptimizationSafetyBounds ((sad - (2 * k_pre ) ) + (2 * k_pre ) ) two blocks ) ”
  &&  “ (MinValue k_pre two k_pre ) ”
  &&  “ ((sad - (2 * k_pre ) ) = (((sad - (2 * k_pre ) ) + (2 * k_pre ) ) - (2 * k_pre ) )) ”
  &&  “ (0 <= k_pre) ”
  &&  “ (k_pre <= k_pre) ”
  &&  “ (0 <= (k_pre - k_pre )) ”
  &&  “ ((k_pre - k_pre ) <= (Zlength (values))) ”
  &&  emp
).

Definition solver_entail_wit_16_2 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks_2: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (sorted_2: (@list Z)) (PreH1 : (Permutation blocks_2 sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = oc)) (PreH4 : (k_pre >= two)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (ones <> 0)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= n_pre)) (PreH15 : ((Zlength (blocks_2)) = oc)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH19 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (ExamJointOptimizationCertificate values sad two blocks_2 )) (PreH22 : (ExamOptimizationSummary values sad two blocks_2 )) (PreH23 : (OptimizationSafetyBounds sad two blocks_2 )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  (IntArray.seg ones 0 oc sorted_2 )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (sorted: (@list Z)) (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (allone = 0) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values ((sad - (2 * two ) ) + (2 * two ) ) two blocks ) ”
  &&  “ (OptimizationSafetyBounds ((sad - (2 * two ) ) + (2 * two ) ) two blocks ) ”
  &&  “ (MinValue k_pre two two ) ”
  &&  “ ((k_pre - two ) = (k_pre - two )) ”
  &&  “ ((sad - (2 * two ) ) = (((sad - (2 * two ) ) + (2 * two ) ) - (2 * two ) )) ”
  &&  “ (0 <= two) ”
  &&  “ (two <= k_pre) ”
  &&  “ (0 <= (k_pre - two )) ”
  &&  “ ((k_pre - two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (blocks_2: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (sorted_2: (@list Z)) (PreH1 : (Permutation blocks_2 sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = oc)) (PreH4 : (k_pre >= two)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (ones <> 0)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= n_pre)) (PreH15 : ((Zlength (blocks_2)) = oc)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values n_pre blocks_2 )) (PreH19 : (JointPairBlockPrefix values n_pre sad two blocks_2 )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks_2 )) (PreH21 : (ExamJointOptimizationCertificate values sad two blocks_2 )) (PreH22 : (ExamOptimizationSummary values sad two blocks_2 )) (PreH23 : (OptimizationSafetyBounds sad two blocks_2 )) (PreH24 : (0 <= sad)) (PreH25 : (sad < n_pre)) (PreH26 : (0 <= two)) (PreH27 : ((2 * two ) <= n_pre)),
  TT && emp 
|--
  EX (blocks: (@list Z)),
  “ ((Zlength (blocks)) = (Zlength (sorted_2))) ”
  &&  “ (Permutation blocks sorted_2 ) ”
  &&  “ (ExamOptimizationSummary values ((sad - (2 * two ) ) + (2 * two ) ) two blocks ) ”
  &&  “ (OptimizationSafetyBounds ((sad - (2 * two ) ) + (2 * two ) ) two blocks ) ”
  &&  “ (MinValue k_pre two two ) ”
  &&  “ ((sad - (2 * two ) ) = (((sad - (2 * two ) ) + (2 * two ) ) - (2 * two ) )) ”
  &&  “ (two <= k_pre) ”
  &&  “ (0 <= (k_pre - two )) ”
  &&  “ ((k_pre - two ) <= (Zlength (values))) ”
  &&  emp
).

Definition solver_entail_wit_17 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks_2: (@list Z)) (sorted_2: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (two: Z) (sad: Z) (use: Z) (k: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (allone = 0)) (PreH6 : (ones <> 0)) (PreH7 : (0 <= oc)) (PreH8 : (oc <= n_pre)) (PreH9 : ((Zlength (blocks_2)) = oc)) (PreH10 : ((Zlength (sorted_2)) = oc)) (PreH11 : (Permutation blocks_2 sorted_2 )) (PreH12 : (increasing sorted_2 )) (PreH13 : (ExamOptimizationSummary values (sad + (2 * use ) ) two blocks_2 )) (PreH14 : (OptimizationSafetyBounds (sad + (2 * use ) ) two blocks_2 )) (PreH15 : (MinValue k_pre two use )) (PreH16 : (k = (k_pre - use ))) (PreH17 : (sad = ((sad + (2 * use ) ) - (2 * use ) ))) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= k)) (PreH21 : (k <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (base_sad: Z) (sorted: (@list Z)) (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (allone = 0) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds base_sad two blocks ) ”
  &&  “ (MinValue k_pre two use ) ”
  &&  “ (0 <= use) ”
  &&  “ (use <= k_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad <= n_pre) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n_pre) ”
  &&  “ (GreedyBlockState sorted 0 (k_pre - use ) (base_sad - (2 * use ) ) k sad ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (blocks_2: (@list Z)) (sorted_2: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (two: Z) (sad: Z) (use: Z) (k: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (allone = 0)) (PreH6 : (ones <> 0)) (PreH7 : (0 <= oc)) (PreH8 : (oc <= n_pre)) (PreH9 : ((Zlength (blocks_2)) = oc)) (PreH10 : ((Zlength (sorted_2)) = oc)) (PreH11 : (Permutation blocks_2 sorted_2 )) (PreH12 : (increasing sorted_2 )) (PreH13 : (ExamOptimizationSummary values (sad + (2 * use ) ) two blocks_2 )) (PreH14 : (OptimizationSafetyBounds (sad + (2 * use ) ) two blocks_2 )) (PreH15 : (MinValue k_pre two use )) (PreH16 : (k = (k_pre - use ))) (PreH17 : (sad = ((sad + (2 * use ) ) - (2 * use ) ))) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= k)) (PreH21 : (k <= n_pre)),
  TT && emp 
|--
  EX (base_sad: Z) (blocks: (@list Z)),
  “ ((Zlength (blocks)) = (Zlength (blocks_2))) ”
  &&  “ (Permutation blocks sorted_2 ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds base_sad two blocks ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((sad + (2 * use ) ) - (2 * use ) )) ”
  &&  “ (((sad + (2 * use ) ) - (2 * use ) ) <= (Zlength (values))) ”
  &&  “ (GreedyBlockState sorted_2 0 (k_pre - use ) (base_sad - (2 * use ) ) (k_pre - use ) ((sad + (2 * use ) ) - (2 * use ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_18 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad_2: Z) (two: Z) (sorted_2: (@list Z)) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted_2 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks_2)) = oc)) (PreH12 : ((Zlength (sorted_2)) = oc)) (PreH13 : (Permutation blocks_2 sorted_2 )) (PreH14 : (increasing sorted_2 )) (PreH15 : (ExamOptimizationSummary values base_sad_2 two blocks_2 )) (PreH16 : (OptimizationSafetyBounds base_sad_2 two blocks_2 )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted_2 i (k_pre - use ) (base_sad_2 - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted_2 )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (base_sad: Z) (sorted: (@list Z)) (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (allone = 0) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds base_sad two blocks ) ”
  &&  “ (MinValue k_pre two use ) ”
  &&  “ (0 <= use) ”
  &&  “ (use <= k_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= oc) ”
  &&  “ (0 <= (sad - ((Znth (i - 0 ) sorted_2 0) + 1 ) )) ”
  &&  “ ((sad - ((Znth (i - 0 ) sorted_2 0) + 1 ) ) <= n_pre) ”
  &&  “ (0 <= (k - (Znth (i - 0 ) sorted_2 0) )) ”
  &&  “ ((k - (Znth (i - 0 ) sorted_2 0) ) <= n_pre) ”
  &&  “ (GreedyBlockState sorted (i + 1 ) (k_pre - use ) (base_sad - (2 * use ) ) (k - (Znth (i - 0 ) sorted_2 0) ) (sad - ((Znth (i - 0 ) sorted_2 0) + 1 ) ) ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad_2: Z) (two: Z) (sorted_2: (@list Z)) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted_2 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks_2)) = oc)) (PreH12 : ((Zlength (sorted_2)) = oc)) (PreH13 : (Permutation blocks_2 sorted_2 )) (PreH14 : (increasing sorted_2 )) (PreH15 : (ExamOptimizationSummary values base_sad_2 two blocks_2 )) (PreH16 : (OptimizationSafetyBounds base_sad_2 two blocks_2 )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted_2 i (k_pre - use ) (base_sad_2 - (2 * use ) ) k sad )),
  TT && emp 
|--
  EX (base_sad: Z) (blocks: (@list Z)),
  “ ((Zlength (blocks)) = (Zlength (blocks_2))) ”
  &&  “ (Permutation blocks sorted_2 ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds base_sad two blocks ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (blocks_2))) ”
  &&  “ (0 <= (sad - ((Znth (i - 0 ) sorted_2 0) + 1 ) )) ”
  &&  “ ((sad - ((Znth (i - 0 ) sorted_2 0) + 1 ) ) <= (Zlength (values))) ”
  &&  “ (0 <= (k - (Znth (i - 0 ) sorted_2 0) )) ”
  &&  “ ((k - (Znth (i - 0 ) sorted_2 0) ) <= (Zlength (values))) ”
  &&  “ (GreedyBlockState sorted_2 (i + 1 ) (k_pre - use ) (base_sad - (2 * use ) ) (k - (Znth (i - 0 ) sorted_2 0) ) (sad - ((Znth (i - 0 ) sorted_2 0) + 1 ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_19_1 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad_2: Z) (two: Z) (sorted_2: (@list Z)) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - sad ) >= 0)) (PreH2 : (k > sad)) (PreH3 : (i >= oc)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (allone = 0)) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks_2)) = oc)) (PreH13 : ((Zlength (sorted_2)) = oc)) (PreH14 : (Permutation blocks_2 sorted_2 )) (PreH15 : (increasing sorted_2 )) (PreH16 : (ExamOptimizationSummary values base_sad_2 two blocks_2 )) (PreH17 : (OptimizationSafetyBounds base_sad_2 two blocks_2 )) (PreH18 : (MinValue k_pre two use )) (PreH19 : (0 <= use)) (PreH20 : (use <= k_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= oc)) (PreH23 : (0 <= sad)) (PreH24 : (sad <= n_pre)) (PreH25 : (0 <= k)) (PreH26 : (k <= n_pre)) (PreH27 : (GreedyBlockState sorted_2 i (k_pre - use ) (base_sad_2 - (2 * use ) ) k sad )),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (base_sad: Z) (sorted: (@list Z)) (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (Spec k_pre values (sad - sad ) ) ”
  &&  “ (0 <= (sad - sad )) ”
  &&  “ ((sad - sad ) < n_pre) ”
  &&  “ (0 <= allone) ”
  &&  “ (allone <= 1) ”
  &&  “ (0 <= use) ”
  &&  “ (use <= n_pre) ”
  &&  “ ((-n_pre) <= sad) ”
  &&  “ (sad <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad_2: Z) (two: Z) (sorted_2: (@list Z)) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - sad ) >= 0)) (PreH2 : (k > sad)) (PreH3 : (i >= oc)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (allone = 0)) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks_2)) = oc)) (PreH13 : ((Zlength (sorted_2)) = oc)) (PreH14 : (Permutation blocks_2 sorted_2 )) (PreH15 : (increasing sorted_2 )) (PreH16 : (ExamOptimizationSummary values base_sad_2 two blocks_2 )) (PreH17 : (OptimizationSafetyBounds base_sad_2 two blocks_2 )) (PreH18 : (MinValue k_pre two use )) (PreH19 : (0 <= use)) (PreH20 : (use <= k_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= oc)) (PreH23 : (0 <= sad)) (PreH24 : (sad <= n_pre)) (PreH25 : (0 <= k)) (PreH26 : (k <= n_pre)) (PreH27 : (GreedyBlockState sorted_2 i (k_pre - use ) (base_sad_2 - (2 * use ) ) k sad )),
  TT && emp 
|--
  EX (base_sad: Z) (blocks: (@list Z)),
  “ ((Zlength (blocks)) = (Zlength (blocks_2))) ”
  &&  “ (Permutation blocks sorted_2 ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (Spec k_pre values (sad - sad ) ) ”
  &&  “ (0 <= (sad - sad )) ”
  &&  “ ((sad - sad ) < (Zlength (values))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ (use <= (Zlength (values))) ”
  &&  “ ((-(Zlength (values))) <= sad) ”
  &&  emp
).

Definition solver_entail_wit_19_2 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad_2: Z) (two: Z) (sorted_2: (@list Z)) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - sad ) >= 0)) (PreH2 : (k > sad)) (PreH3 : ((Znth (i - 0 ) sorted_2 0) > k)) (PreH4 : (i < oc)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (allone = 0)) (PreH10 : (ones <> 0)) (PreH11 : (0 <= oc)) (PreH12 : (oc <= n_pre)) (PreH13 : ((Zlength (blocks_2)) = oc)) (PreH14 : ((Zlength (sorted_2)) = oc)) (PreH15 : (Permutation blocks_2 sorted_2 )) (PreH16 : (increasing sorted_2 )) (PreH17 : (ExamOptimizationSummary values base_sad_2 two blocks_2 )) (PreH18 : (OptimizationSafetyBounds base_sad_2 two blocks_2 )) (PreH19 : (MinValue k_pre two use )) (PreH20 : (0 <= use)) (PreH21 : (use <= k_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= oc)) (PreH24 : (0 <= sad)) (PreH25 : (sad <= n_pre)) (PreH26 : (0 <= k)) (PreH27 : (k <= n_pre)) (PreH28 : (GreedyBlockState sorted_2 i (k_pre - use ) (base_sad_2 - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted_2 )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (base_sad: Z) (sorted: (@list Z)) (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (Spec k_pre values (sad - sad ) ) ”
  &&  “ (0 <= (sad - sad )) ”
  &&  “ ((sad - sad ) < n_pre) ”
  &&  “ (0 <= allone) ”
  &&  “ (allone <= 1) ”
  &&  “ (0 <= use) ”
  &&  “ (use <= n_pre) ”
  &&  “ ((-n_pre) <= sad) ”
  &&  “ (sad <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad_2: Z) (two: Z) (sorted_2: (@list Z)) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - sad ) >= 0)) (PreH2 : (k > sad)) (PreH3 : ((Znth (i - 0 ) sorted_2 0) > k)) (PreH4 : (i < oc)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (allone = 0)) (PreH10 : (ones <> 0)) (PreH11 : (0 <= oc)) (PreH12 : (oc <= n_pre)) (PreH13 : ((Zlength (blocks_2)) = oc)) (PreH14 : ((Zlength (sorted_2)) = oc)) (PreH15 : (Permutation blocks_2 sorted_2 )) (PreH16 : (increasing sorted_2 )) (PreH17 : (ExamOptimizationSummary values base_sad_2 two blocks_2 )) (PreH18 : (OptimizationSafetyBounds base_sad_2 two blocks_2 )) (PreH19 : (MinValue k_pre two use )) (PreH20 : (0 <= use)) (PreH21 : (use <= k_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= oc)) (PreH24 : (0 <= sad)) (PreH25 : (sad <= n_pre)) (PreH26 : (0 <= k)) (PreH27 : (k <= n_pre)) (PreH28 : (GreedyBlockState sorted_2 i (k_pre - use ) (base_sad_2 - (2 * use ) ) k sad )),
  TT && emp 
|--
  EX (base_sad: Z) (blocks: (@list Z)),
  “ ((Zlength (blocks)) = (Zlength (blocks_2))) ”
  &&  “ (Permutation blocks sorted_2 ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (Spec k_pre values (sad - sad ) ) ”
  &&  “ (0 <= (sad - sad )) ”
  &&  “ ((sad - sad ) < (Zlength (values))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ (use <= (Zlength (values))) ”
  &&  “ ((-(Zlength (values))) <= sad) ”
  &&  emp
).

Definition solver_entail_wit_19_3 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad_2: Z) (two: Z) (sorted_2: (@list Z)) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - k ) >= 0)) (PreH2 : (k <= sad)) (PreH3 : (i >= oc)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (allone = 0)) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks_2)) = oc)) (PreH13 : ((Zlength (sorted_2)) = oc)) (PreH14 : (Permutation blocks_2 sorted_2 )) (PreH15 : (increasing sorted_2 )) (PreH16 : (ExamOptimizationSummary values base_sad_2 two blocks_2 )) (PreH17 : (OptimizationSafetyBounds base_sad_2 two blocks_2 )) (PreH18 : (MinValue k_pre two use )) (PreH19 : (0 <= use)) (PreH20 : (use <= k_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= oc)) (PreH23 : (0 <= sad)) (PreH24 : (sad <= n_pre)) (PreH25 : (0 <= k)) (PreH26 : (k <= n_pre)) (PreH27 : (GreedyBlockState sorted_2 i (k_pre - use ) (base_sad_2 - (2 * use ) ) k sad )),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted_2 )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (base_sad: Z) (sorted: (@list Z)) (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (Spec k_pre values (sad - k ) ) ”
  &&  “ (0 <= (sad - k )) ”
  &&  “ ((sad - k ) < n_pre) ”
  &&  “ (0 <= allone) ”
  &&  “ (allone <= 1) ”
  &&  “ (0 <= use) ”
  &&  “ (use <= n_pre) ”
  &&  “ ((-n_pre) <= k) ”
  &&  “ (k <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad_2: Z) (two: Z) (sorted_2: (@list Z)) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - k ) >= 0)) (PreH2 : (k <= sad)) (PreH3 : (i >= oc)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (allone = 0)) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks_2)) = oc)) (PreH13 : ((Zlength (sorted_2)) = oc)) (PreH14 : (Permutation blocks_2 sorted_2 )) (PreH15 : (increasing sorted_2 )) (PreH16 : (ExamOptimizationSummary values base_sad_2 two blocks_2 )) (PreH17 : (OptimizationSafetyBounds base_sad_2 two blocks_2 )) (PreH18 : (MinValue k_pre two use )) (PreH19 : (0 <= use)) (PreH20 : (use <= k_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= oc)) (PreH23 : (0 <= sad)) (PreH24 : (sad <= n_pre)) (PreH25 : (0 <= k)) (PreH26 : (k <= n_pre)) (PreH27 : (GreedyBlockState sorted_2 i (k_pre - use ) (base_sad_2 - (2 * use ) ) k sad )),
  TT && emp 
|--
  EX (base_sad: Z) (blocks: (@list Z)),
  “ ((Zlength (blocks)) = (Zlength (blocks_2))) ”
  &&  “ (Permutation blocks sorted_2 ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (Spec k_pre values (sad - k ) ) ”
  &&  “ (0 <= (sad - k )) ”
  &&  “ ((sad - k ) < (Zlength (values))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ (use <= (Zlength (values))) ”
  &&  “ ((-(Zlength (values))) <= k) ”
  &&  emp
).

Definition solver_entail_wit_19_4 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad_2: Z) (two: Z) (sorted_2: (@list Z)) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - k ) >= 0)) (PreH2 : (k <= sad)) (PreH3 : ((Znth (i - 0 ) sorted_2 0) > k)) (PreH4 : (i < oc)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (allone = 0)) (PreH10 : (ones <> 0)) (PreH11 : (0 <= oc)) (PreH12 : (oc <= n_pre)) (PreH13 : ((Zlength (blocks_2)) = oc)) (PreH14 : ((Zlength (sorted_2)) = oc)) (PreH15 : (Permutation blocks_2 sorted_2 )) (PreH16 : (increasing sorted_2 )) (PreH17 : (ExamOptimizationSummary values base_sad_2 two blocks_2 )) (PreH18 : (OptimizationSafetyBounds base_sad_2 two blocks_2 )) (PreH19 : (MinValue k_pre two use )) (PreH20 : (0 <= use)) (PreH21 : (use <= k_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= oc)) (PreH24 : (0 <= sad)) (PreH25 : (sad <= n_pre)) (PreH26 : (0 <= k)) (PreH27 : (k <= n_pre)) (PreH28 : (GreedyBlockState sorted_2 i (k_pre - use ) (base_sad_2 - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted_2 )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  EX (base_sad: Z) (sorted: (@list Z)) (blocks: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (Spec k_pre values (sad - k ) ) ”
  &&  “ (0 <= (sad - k )) ”
  &&  “ ((sad - k ) < n_pre) ”
  &&  “ (0 <= allone) ”
  &&  “ (allone <= 1) ”
  &&  “ (0 <= use) ”
  &&  “ (use <= n_pre) ”
  &&  “ ((-n_pre) <= k) ”
  &&  “ (k <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad_2: Z) (two: Z) (sorted_2: (@list Z)) (blocks_2: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((sad - k ) >= 0)) (PreH2 : (k <= sad)) (PreH3 : ((Znth (i - 0 ) sorted_2 0) > k)) (PreH4 : (i < oc)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (allone = 0)) (PreH10 : (ones <> 0)) (PreH11 : (0 <= oc)) (PreH12 : (oc <= n_pre)) (PreH13 : ((Zlength (blocks_2)) = oc)) (PreH14 : ((Zlength (sorted_2)) = oc)) (PreH15 : (Permutation blocks_2 sorted_2 )) (PreH16 : (increasing sorted_2 )) (PreH17 : (ExamOptimizationSummary values base_sad_2 two blocks_2 )) (PreH18 : (OptimizationSafetyBounds base_sad_2 two blocks_2 )) (PreH19 : (MinValue k_pre two use )) (PreH20 : (0 <= use)) (PreH21 : (use <= k_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= oc)) (PreH24 : (0 <= sad)) (PreH25 : (sad <= n_pre)) (PreH26 : (0 <= k)) (PreH27 : (k <= n_pre)) (PreH28 : (GreedyBlockState sorted_2 i (k_pre - use ) (base_sad_2 - (2 * use ) ) k sad )),
  TT && emp 
|--
  EX (base_sad: Z) (blocks: (@list Z)),
  “ ((Zlength (blocks)) = (Zlength (blocks_2))) ”
  &&  “ (Permutation blocks sorted_2 ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (Spec k_pre values (sad - k ) ) ”
  &&  “ (0 <= (sad - k )) ”
  &&  “ ((sad - k ) < (Zlength (values))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ (use <= (Zlength (values))) ”
  &&  “ ((-(Zlength (values))) <= k) ”
  &&  emp
).

Definition solver_return_wit_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (sorted: (@list Z)) (base_sad: Z) (ones: Z) (oc: Z) (two: Z) (sad: Z) (allone: Z) (use: Z) (k: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (ones <> 0)) (PreH6 : (0 <= oc)) (PreH7 : (oc <= n_pre)) (PreH8 : ((Zlength (blocks)) = oc)) (PreH9 : ((Zlength (sorted)) = oc)) (PreH10 : (Permutation blocks sorted )) (PreH11 : (increasing sorted )) (PreH12 : (ExamOptimizationSummary values base_sad two blocks )) (PreH13 : (Spec k_pre values sad )) (PreH14 : (0 <= sad)) (PreH15 : (sad < n_pre)) (PreH16 : (0 <= allone)) (PreH17 : (allone <= 1)) (PreH18 : (0 <= use)) (PreH19 : (use <= n_pre)) (PreH20 : ((-n_pre) <= k)) (PreH21 : (k <= n_pre)),
  (Int64Array.full a_pre n_pre values )
|--
  “ (Spec k_pre values sad ) ”
  &&  (Int64Array.full a_pre n_pre values )
.

Definition solver_return_wit_2 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : (k_pre = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )) (PreH13 : (allone <> 0)),
  (Int64Array.full a_pre n_pre values )
|--
  “ (Spec k_pre values 0 ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : (k_pre = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )) (PreH13 : (allone <> 0)),
  TT && emp 
|--
  “ (Spec n_pre values 0 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : (k_pre = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )) (PreH13 : (allone <> 0)),
  (Spec n_pre values 0 )
.

Definition solver_return_wit_3 :=
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : (k_pre <> n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )) (PreH13 : (allone <> 0)),
  (Int64Array.full a_pre n_pre values )
|--
  “ (Spec k_pre values (n_pre - k_pre ) ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : (k_pre <> n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )) (PreH13 : (allone <> 0)),
  TT && emp 
|--
  “ (Spec k_pre values (n_pre - k_pre ) ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (allone: Z) (i: Z) (PreH1 : (k_pre <> n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= allone)) (PreH11 : (allone <= 1)) (PreH12 : (AllOnePrefix values i allone )) (PreH13 : (allone <> 0)),
  (Spec k_pre values (n_pre - k_pre ) )
.

Definition solver_partial_solve_wit_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= allone)) (PreH10 : (allone <= 1)) (PreH11 : (AllOnePrefix values i allone )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= allone) ”
  &&  “ (allone <= 1) ”
  &&  “ (AllOnePrefix values i allone ) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (two = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (0 <= sad)) (PreH13 : (sad <= i)) (PreH14 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (two = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad <= i) ”
  &&  “ (CoprimeEdgePrefixCount values i sad ) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (two = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (0 <= sad)) (PreH13 : (sad <= i)) (PreH14 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (two = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad <= i) ”
  &&  “ (CoprimeEdgePrefixCount values i sad ) ”
  &&  (((a_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (i + 1 ) values 0))
  **  (Int64Array.missing_i a_pre (i + 1 ) 0 n_pre values )
.

Definition solver_partial_solve_wit_4_pure :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (two = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (0 <= sad)) (PreH13 : (sad <= i)) (PreH14 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sad" ) )) # Int  |-> sad)
|--
  “ (0 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ (0 <= (Znth (i + 1 ) values 0)) ”
  &&  “ ((Znth (i + 1 ) values 0) <= 1000000000) ”
.

Definition solver_partial_solve_wit_4_aux :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (sad: Z) (i: Z) (two: Z) (allone: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (two = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (0 <= sad)) (PreH13 : (sad <= i)) (PreH14 : (CoprimeEdgePrefixCount values i sad )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ (0 <= (Znth (i + 1 ) values 0)) ”
  &&  “ ((Znth (i + 1 ) values 0) <= 1000000000) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (two = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad <= i) ”
  &&  “ (CoprimeEdgePrefixCount values i sad ) ”
  &&  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth (i - 1 ) values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i) ”
  &&  “ ((Znth (i - 1 ) values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i two ) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_6 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : ((Znth i values 0) = 1)) (PreH17 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i) ”
  &&  “ ((Znth i values 0) = 1) ”
  &&  “ (PairSavingsPrefix values i two ) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_7 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= two)) (PreH15 : ((2 * two ) <= i)) (PreH16 : (i = 0)) (PreH17 : (PairSavingsPrefix values i two )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= i) ”
  &&  “ (i = 0) ”
  &&  “ (PairSavingsPrefix values i two ) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_8 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH10 : (0 <= sad)) (PreH11 : (sad < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= two)) (PreH15 : (0 <= run)) (PreH16 : (run <= (i + 1 ))) (PreH17 : (PairRunSuffix values (i + 1 ) run )) (PreH18 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH19 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ (0 <= run) ”
  &&  “ (run <= (i + 1 )) ”
  &&  “ (PairRunSuffix values (i + 1 ) run ) ”
  &&  “ (scan_savings = (two + (run ÷ 2 ) )) ”
  &&  “ (PairSavingsScan values (i + 1 ) two run scan_savings ) ”
  &&  (((a_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (i + 1 ) values 0))
  **  (Int64Array.missing_i a_pre (i + 1 ) 0 n_pre values )
.

Definition solver_partial_solve_wit_9 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) <> 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
|--
  “ ((Znth (i + 1 ) values 0) <> 1) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ (0 <= run) ”
  &&  “ (run <= (i + 1 )) ”
  &&  “ (PairRunSuffix values (i + 1 ) run ) ”
  &&  “ (scan_savings = (two + (run ÷ 2 ) )) ”
  &&  “ (PairSavingsScan values (i + 1 ) two run scan_savings ) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_10 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) <> 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
|--
  “ ((Znth (i + 1 ) values 0) <> 1) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ (0 <= run) ”
  &&  “ (run <= (i + 1 )) ”
  &&  “ (PairRunSuffix values (i + 1 ) run ) ”
  &&  “ (scan_savings = (two + (run ÷ 2 ) )) ”
  &&  “ (PairSavingsScan values (i + 1 ) two run scan_savings ) ”
  &&  (((a_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (i + 1 ) values 0))
  **  (Int64Array.missing_i a_pre (i + 1 ) 0 n_pre values )
.

Definition solver_partial_solve_wit_11_pure :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) <> 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "run" ) )) # Int  |-> run)
|--
  “ (0 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ (0 <= (Znth (i + 1 ) values 0)) ”
  &&  “ ((Znth (i + 1 ) values 0) <= 1000000000) ”
.

Definition solver_partial_solve_wit_11_aux :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (scan_savings: Z) (run: Z) (two: Z) (i: Z) (sad: Z) (allone: Z) (PreH1 : ((Znth (i + 1 ) values 0) <> 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH8 : (allone = 0)) (PreH9 : (AllOnePrefix values n_pre allone )) (PreH10 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= two)) (PreH16 : (0 <= run)) (PreH17 : (run <= (i + 1 ))) (PreH18 : (PairRunSuffix values (i + 1 ) run )) (PreH19 : (scan_savings = (two + (run ÷ 2 ) ))) (PreH20 : (PairSavingsScan values (i + 1 ) two run scan_savings )),
  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ (0 <= (Znth (i + 1 ) values 0)) ”
  &&  “ ((Znth (i + 1 ) values 0) <= 1000000000) ”
  &&  “ ((Znth (i + 1 ) values 0) <> 1) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ (0 <= run) ”
  &&  “ (run <= (i + 1 )) ”
  &&  “ (PairRunSuffix values (i + 1 ) run ) ”
  &&  “ (scan_savings = (two + (run ÷ 2 ) )) ”
  &&  “ (PairSavingsScan values (i + 1 ) two run scan_savings ) ”
  &&  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_11 := solver_partial_solve_wit_11_pure -> solver_partial_solve_wit_11_aux.

Definition solver_partial_solve_wit_12_pure :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (sad: Z) (two: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH6 : (allone = 0)) (PreH7 : (AllOnePrefix values n_pre allone )) (PreH8 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH9 : (PairSavingsPrefix values n_pre two )) (PreH10 : (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= two)) (PreH14 : ((2 * two ) <= n_pre)),
  ((( &( "ones" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= n_pre) ”
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_12_aux :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (allone: Z) (sad: Z) (two: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH6 : (allone = 0)) (PreH7 : (AllOnePrefix values n_pre allone )) (PreH8 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH9 : (PairSavingsPrefix values n_pre two )) (PreH10 : (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) )) (PreH11 : (0 <= sad)) (PreH12 : (sad < n_pre)) (PreH13 : (0 <= two)) (PreH14 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= n_pre) ”
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two (@nil Z) ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_12 := solver_partial_solve_wit_12_pure -> solver_partial_solve_wit_12_aux.

Definition solver_partial_solve_wit_13 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks)) = oc)) (PreH15 : ((Znth (i - 1 ) values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH19 : (JointPairBlockPrefix values i sad two blocks )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (i - 1 ) values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
.

Definition solver_partial_solve_wit_14 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks)) = oc)) (PreH15 : ((Znth i values 0) <> 1)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH19 : (JointPairBlockPrefix values i sad two blocks )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth i values 0) <> 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
.

Definition solver_partial_solve_wit_15 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= oc)) (PreH13 : (oc <= i)) (PreH14 : ((Zlength (blocks)) = oc)) (PreH15 : (i = 0)) (PreH16 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH17 : (PairSavingsPrefix values n_pre two )) (PreH18 : (CanonicalInteriorOneRunPrefix values i blocks )) (PreH19 : (JointPairBlockPrefix values i sad two blocks )) (PreH20 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= i) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (i = 0) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values i blocks ) ”
  &&  “ (JointPairBlockPrefix values i sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
.

Definition solver_partial_solve_wit_16 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= l)) (PreH11 : (l <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= l)) (PreH15 : ((Zlength (blocks)) = oc)) (PreH16 : ((Znth (l - 1 ) values 0) <> 1)) (PreH17 : ((Znth l values 0) = 1)) (PreH18 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH19 : (PairSavingsPrefix values n_pre two )) (PreH20 : (CanonicalOneRunScanState values l i blocks )) (PreH21 : (JointPairBlockPrefix values l sad two blocks )) (PreH22 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH23 : (0 <= sad)) (PreH24 : (sad < n_pre)) (PreH25 : (0 <= two)) (PreH26 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= l) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (l - 1 ) values 0) <> 1) ”
  &&  “ ((Znth l values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values l i blocks ) ”
  &&  “ (JointPairBlockPrefix values l sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
.

Definition solver_partial_solve_wit_17 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= l)) (PreH11 : (l <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= oc)) (PreH14 : (oc <= l)) (PreH15 : ((Zlength (blocks)) = oc)) (PreH16 : (l = 0)) (PreH17 : ((Znth l values 0) = 1)) (PreH18 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH19 : (PairSavingsPrefix values n_pre two )) (PreH20 : (CanonicalOneRunScanState values l i blocks )) (PreH21 : (JointPairBlockPrefix values l sad two blocks )) (PreH22 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH23 : (0 <= sad)) (PreH24 : (sad < n_pre)) (PreH25 : (0 <= two)) (PreH26 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= l) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (l = 0) ”
  &&  “ ((Znth l values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values l i blocks ) ”
  &&  “ (JointPairBlockPrefix values l sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
.

Definition solver_partial_solve_wit_18 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (two: Z) (sad: Z) (blocks: (@list Z)) (oc: Z) (i: Z) (l: Z) (ones: Z) (allone: Z) (PreH1 : (i < n_pre)) (PreH2 : (l > 0)) (PreH3 : ((Znth i values 0) <> 1)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (allone = 0)) (PreH11 : (AllOnePrefix values n_pre allone )) (PreH12 : (ones <> 0)) (PreH13 : (0 <= l)) (PreH14 : (l <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= oc)) (PreH17 : (oc <= l)) (PreH18 : ((Zlength (blocks)) = oc)) (PreH19 : ((Znth (l - 1 ) values 0) <> 1)) (PreH20 : ((Znth l values 0) = 1)) (PreH21 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH22 : (PairSavingsPrefix values n_pre two )) (PreH23 : (CanonicalOneRunScanState values l i blocks )) (PreH24 : (JointPairBlockPrefix values l sad two blocks )) (PreH25 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH26 : (0 <= sad)) (PreH27 : (sad < n_pre)) (PreH28 : (0 <= two)) (PreH29 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (l > 0) ”
  &&  “ ((Znth i values 0) <> 1) ”
  &&  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= l) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Znth (l - 1 ) values 0) <> 1) ”
  &&  “ ((Znth l values 0) = 1) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalOneRunScanState values l i blocks ) ”
  &&  “ (JointPairBlockPrefix values l sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (((ones + (oc * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ones (oc + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
.

Definition solver_partial_solve_wit_19_pure :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre < two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "use" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> (k_pre - k_pre ))
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> (sad - (2 * k_pre ) ))
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (oc = (Zlength (blocks))) ”
  &&  “ (sizeof(INT) = sizeof(INT)) ”
.

Definition solver_partial_solve_wit_19_aux :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre < two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (oc = (Zlength (blocks))) ”
  &&  “ (sizeof(INT) = sizeof(INT)) ”
  &&  “ (k_pre < two) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (ExamJointOptimizationCertificate values sad two blocks ) ”
  &&  “ (ExamOptimizationSummary values sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (IntArray.seg ones 0 oc blocks )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
.

Definition solver_partial_solve_wit_19 := solver_partial_solve_wit_19_pure -> solver_partial_solve_wit_19_aux.

Definition solver_partial_solve_wit_20_pure :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre >= two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  ((( &( "use" ) )) # Int  |-> two)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> (k_pre - two ))
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "sad" ) )) # Int  |-> (sad - (2 * two ) ))
  **  ((( &( "two" ) )) # Int  |-> two)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (oc = (Zlength (blocks))) ”
  &&  “ (sizeof(INT) = sizeof(INT)) ”
.

Definition solver_partial_solve_wit_20_aux :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (allone: Z) (ones: Z) (oc: Z) (sad: Z) (two: Z) (PreH1 : (k_pre >= two)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH7 : (allone = 0)) (PreH8 : (AllOnePrefix values n_pre allone )) (PreH9 : (ones <> 0)) (PreH10 : (0 <= oc)) (PreH11 : (oc <= n_pre)) (PreH12 : ((Zlength (blocks)) = oc)) (PreH13 : (CoprimeEdgePrefixCount values (n_pre - 1 ) sad )) (PreH14 : (PairSavingsPrefix values n_pre two )) (PreH15 : (CanonicalInteriorOneRunPrefix values n_pre blocks )) (PreH16 : (JointPairBlockPrefix values n_pre sad two blocks )) (PreH17 : (CanonicalExamBlockCollectionCertificate values sad two blocks )) (PreH18 : (ExamJointOptimizationCertificate values sad two blocks )) (PreH19 : (ExamOptimizationSummary values sad two blocks )) (PreH20 : (OptimizationSafetyBounds sad two blocks )) (PreH21 : (0 <= sad)) (PreH22 : (sad < n_pre)) (PreH23 : (0 <= two)) (PreH24 : ((2 * two ) <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc blocks )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (oc = (Zlength (blocks))) ”
  &&  “ (sizeof(INT) = sizeof(INT)) ”
  &&  “ (k_pre >= two) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  “ (allone = 0) ”
  &&  “ (AllOnePrefix values n_pre allone ) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ (CoprimeEdgePrefixCount values (n_pre - 1 ) sad ) ”
  &&  “ (PairSavingsPrefix values n_pre two ) ”
  &&  “ (CanonicalInteriorOneRunPrefix values n_pre blocks ) ”
  &&  “ (JointPairBlockPrefix values n_pre sad two blocks ) ”
  &&  “ (CanonicalExamBlockCollectionCertificate values sad two blocks ) ”
  &&  “ (ExamJointOptimizationCertificate values sad two blocks ) ”
  &&  “ (ExamOptimizationSummary values sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds sad two blocks ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= two) ”
  &&  “ ((2 * two ) <= n_pre) ”
  &&  (IntArray.seg ones 0 oc blocks )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
.

Definition solver_partial_solve_wit_20 := solver_partial_solve_wit_20_pure -> solver_partial_solve_wit_20_aux.

Definition solver_partial_solve_wit_21 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : (i < oc)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (allone = 0)) (PreH7 : (ones <> 0)) (PreH8 : (0 <= oc)) (PreH9 : (oc <= n_pre)) (PreH10 : ((Zlength (blocks)) = oc)) (PreH11 : ((Zlength (sorted)) = oc)) (PreH12 : (Permutation blocks sorted )) (PreH13 : (increasing sorted )) (PreH14 : (ExamOptimizationSummary values base_sad two blocks )) (PreH15 : (OptimizationSafetyBounds base_sad two blocks )) (PreH16 : (MinValue k_pre two use )) (PreH17 : (0 <= use)) (PreH18 : (use <= k_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= oc)) (PreH21 : (0 <= sad)) (PreH22 : (sad <= n_pre)) (PreH23 : (0 <= k)) (PreH24 : (k <= n_pre)) (PreH25 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (i < oc) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (allone = 0) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds base_sad two blocks ) ”
  &&  “ (MinValue k_pre two use ) ”
  &&  “ (0 <= use) ”
  &&  “ (use <= k_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= oc) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad <= n_pre) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n_pre) ”
  &&  “ (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad ) ”
  &&  (((ones + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) sorted 0))
  **  (IntArray.missing_i ones i 0 oc sorted )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
.

Definition solver_partial_solve_wit_22 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((Znth (i - 0 ) sorted 0) <= k) ”
  &&  “ (i < oc) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (allone = 0) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds base_sad two blocks ) ”
  &&  “ (MinValue k_pre two use ) ”
  &&  “ (0 <= use) ”
  &&  “ (use <= k_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= oc) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad <= n_pre) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n_pre) ”
  &&  “ (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad ) ”
  &&  (((ones + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) sorted 0))
  **  (IntArray.missing_i ones i 0 oc sorted )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
.

Definition solver_partial_solve_wit_23 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (k: Z) (sad: Z) (i: Z) (use: Z) (base_sad: Z) (two: Z) (sorted: (@list Z)) (blocks: (@list Z)) (oc: Z) (ones: Z) (allone: Z) (PreH1 : ((Znth (i - 0 ) sorted 0) <= k)) (PreH2 : (i < oc)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (allone = 0)) (PreH8 : (ones <> 0)) (PreH9 : (0 <= oc)) (PreH10 : (oc <= n_pre)) (PreH11 : ((Zlength (blocks)) = oc)) (PreH12 : ((Zlength (sorted)) = oc)) (PreH13 : (Permutation blocks sorted )) (PreH14 : (increasing sorted )) (PreH15 : (ExamOptimizationSummary values base_sad two blocks )) (PreH16 : (OptimizationSafetyBounds base_sad two blocks )) (PreH17 : (MinValue k_pre two use )) (PreH18 : (0 <= use)) (PreH19 : (use <= k_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= oc)) (PreH22 : (0 <= sad)) (PreH23 : (sad <= n_pre)) (PreH24 : (0 <= k)) (PreH25 : (k <= n_pre)) (PreH26 : (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad )),
  (IntArray.seg ones 0 oc sorted )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ ((Znth (i - 0 ) sorted 0) <= k) ”
  &&  “ (i < oc) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (allone = 0) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (OptimizationSafetyBounds base_sad two blocks ) ”
  &&  “ (MinValue k_pre two use ) ”
  &&  “ (0 <= use) ”
  &&  “ (use <= k_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= oc) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad <= n_pre) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n_pre) ”
  &&  “ (GreedyBlockState sorted i (k_pre - use ) (base_sad - (2 * use ) ) k sad ) ”
  &&  (((ones + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) sorted 0))
  **  (IntArray.missing_i ones i 0 oc sorted )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.undef_seg ones oc n_pre )
.

Definition solver_partial_solve_wit_24_pure :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (sorted: (@list Z)) (base_sad: Z) (ones: Z) (oc: Z) (two: Z) (sad: Z) (allone: Z) (use: Z) (k: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (ones <> 0)) (PreH6 : (0 <= oc)) (PreH7 : (oc <= n_pre)) (PreH8 : ((Zlength (blocks)) = oc)) (PreH9 : ((Zlength (sorted)) = oc)) (PreH10 : (Permutation blocks sorted )) (PreH11 : (increasing sorted )) (PreH12 : (ExamOptimizationSummary values base_sad two blocks )) (PreH13 : (Spec k_pre values sad )) (PreH14 : (0 <= sad)) (PreH15 : (sad < n_pre)) (PreH16 : (0 <= allone)) (PreH17 : (allone <= 1)) (PreH18 : (0 <= use)) (PreH19 : (use <= n_pre)) (PreH20 : ((-n_pre) <= k)) (PreH21 : (k <= n_pre)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ones" ) )) # Ptr  |-> ones)
  **  ((( &( "oc" ) )) # Int  |-> oc)
  **  ((( &( "two" ) )) # Int  |-> two)
  **  ((( &( "sad" ) )) # Int  |-> sad)
  **  ((( &( "allone" ) )) # Int  |-> allone)
  **  ((( &( "use" ) )) # Int  |-> use)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= (Zlength (blocks))) ”
  &&  “ ((Zlength (blocks)) <= (Zlength (values))) ”
.

Definition solver_partial_solve_wit_24_aux :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (a_pre: Z) (blocks: (@list Z)) (sorted: (@list Z)) (base_sad: Z) (ones: Z) (oc: Z) (two: Z) (sad: Z) (allone: Z) (use: Z) (k: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (ones <> 0)) (PreH6 : (0 <= oc)) (PreH7 : (oc <= n_pre)) (PreH8 : ((Zlength (blocks)) = oc)) (PreH9 : ((Zlength (sorted)) = oc)) (PreH10 : (Permutation blocks sorted )) (PreH11 : (increasing sorted )) (PreH12 : (ExamOptimizationSummary values base_sad two blocks )) (PreH13 : (Spec k_pre values sad )) (PreH14 : (0 <= sad)) (PreH15 : (sad < n_pre)) (PreH16 : (0 <= allone)) (PreH17 : (allone <= 1)) (PreH18 : (0 <= use)) (PreH19 : (use <= n_pre)) (PreH20 : ((-n_pre) <= k)) (PreH21 : (k <= n_pre)),
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.seg ones 0 oc sorted )
  **  (IntArray.undef_seg ones oc n_pre )
|--
  “ (0 <= (Zlength (blocks))) ”
  &&  “ ((Zlength (blocks)) <= (Zlength (values))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (ones <> 0) ”
  &&  “ (0 <= oc) ”
  &&  “ (oc <= n_pre) ”
  &&  “ ((Zlength (blocks)) = oc) ”
  &&  “ ((Zlength (sorted)) = oc) ”
  &&  “ (Permutation blocks sorted ) ”
  &&  “ (increasing sorted ) ”
  &&  “ (ExamOptimizationSummary values base_sad two blocks ) ”
  &&  “ (Spec k_pre values sad ) ”
  &&  “ (0 <= sad) ”
  &&  “ (sad < n_pre) ”
  &&  “ (0 <= allone) ”
  &&  “ (allone <= 1) ”
  &&  “ (0 <= use) ”
  &&  “ (use <= n_pre) ”
  &&  “ ((-n_pre) <= k) ”
  &&  “ (k <= n_pre) ”
  &&  (IntArray.seg ones 0 (Zlength (blocks)) sorted )
  **  (IntArray.undef_seg ones (Zlength (blocks)) (Zlength (values)) )
  **  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_24 := solver_partial_solve_wit_24_pure -> solver_partial_solve_wit_24_aux.

Module Type VC_Correct.


Axiom proof_of_gcdll_safety_wit_1 : gcdll_safety_wit_1.
Axiom proof_of_gcdll_entail_wit_1 : gcdll_entail_wit_1.
Axiom proof_of_gcdll_entail_wit_2 : gcdll_entail_wit_2.
Axiom proof_of_gcdll_return_wit_1 : gcdll_return_wit_1.
Axiom proof_of_cmpi_safety_wit_1 : cmpi_safety_wit_1.
Axiom proof_of_cmpi_return_wit_1 : cmpi_return_wit_1.
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
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Axiom proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Axiom proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Axiom proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Axiom proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Axiom proof_of_solver_safety_wit_50 : solver_safety_wit_50.
Axiom proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Axiom proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Axiom proof_of_solver_safety_wit_53 : solver_safety_wit_53.
Axiom proof_of_solver_safety_wit_54 : solver_safety_wit_54.
Axiom proof_of_solver_safety_wit_55 : solver_safety_wit_55.
Axiom proof_of_solver_safety_wit_56 : solver_safety_wit_56.
Axiom proof_of_solver_safety_wit_57 : solver_safety_wit_57.
Axiom proof_of_solver_safety_wit_58 : solver_safety_wit_58.
Axiom proof_of_solver_safety_wit_59 : solver_safety_wit_59.
Axiom proof_of_solver_safety_wit_60 : solver_safety_wit_60.
Axiom proof_of_solver_safety_wit_61 : solver_safety_wit_61.
Axiom proof_of_solver_safety_wit_62 : solver_safety_wit_62.
Axiom proof_of_solver_safety_wit_63 : solver_safety_wit_63.
Axiom proof_of_solver_safety_wit_64 : solver_safety_wit_64.
Axiom proof_of_solver_safety_wit_65 : solver_safety_wit_65.
Axiom proof_of_solver_safety_wit_66 : solver_safety_wit_66.
Axiom proof_of_solver_safety_wit_67 : solver_safety_wit_67.
Axiom proof_of_solver_safety_wit_68 : solver_safety_wit_68.
Axiom proof_of_solver_safety_wit_69 : solver_safety_wit_69.
Axiom proof_of_solver_safety_wit_70 : solver_safety_wit_70.
Axiom proof_of_solver_safety_wit_71 : solver_safety_wit_71.
Axiom proof_of_solver_safety_wit_72 : solver_safety_wit_72.
Axiom proof_of_solver_safety_wit_73 : solver_safety_wit_73.
Axiom proof_of_solver_safety_wit_74 : solver_safety_wit_74.
Axiom proof_of_solver_safety_wit_75 : solver_safety_wit_75.
Axiom proof_of_solver_safety_wit_76 : solver_safety_wit_76.
Axiom proof_of_solver_safety_wit_77 : solver_safety_wit_77.
Axiom proof_of_solver_safety_wit_78 : solver_safety_wit_78.
Axiom proof_of_solver_safety_wit_79 : solver_safety_wit_79.
Axiom proof_of_solver_safety_wit_80 : solver_safety_wit_80.
Axiom proof_of_solver_safety_wit_81 : solver_safety_wit_81.
Axiom proof_of_solver_safety_wit_82 : solver_safety_wit_82.
Axiom proof_of_solver_safety_wit_83 : solver_safety_wit_83.
Axiom proof_of_solver_safety_wit_84 : solver_safety_wit_84.
Axiom proof_of_solver_safety_wit_85 : solver_safety_wit_85.
Axiom proof_of_solver_safety_wit_86 : solver_safety_wit_86.
Axiom proof_of_solver_safety_wit_87 : solver_safety_wit_87.
Axiom proof_of_solver_safety_wit_88 : solver_safety_wit_88.
Axiom proof_of_solver_safety_wit_89 : solver_safety_wit_89.
Axiom proof_of_solver_safety_wit_90 : solver_safety_wit_90.
Axiom proof_of_solver_safety_wit_91 : solver_safety_wit_91.
Axiom proof_of_solver_safety_wit_92 : solver_safety_wit_92.
Axiom proof_of_solver_safety_wit_93 : solver_safety_wit_93.
Axiom proof_of_solver_safety_wit_94 : solver_safety_wit_94.
Axiom proof_of_solver_safety_wit_95 : solver_safety_wit_95.
Axiom proof_of_solver_safety_wit_96 : solver_safety_wit_96.
Axiom proof_of_solver_safety_wit_97 : solver_safety_wit_97.
Axiom proof_of_solver_safety_wit_98 : solver_safety_wit_98.
Axiom proof_of_solver_safety_wit_99 : solver_safety_wit_99.
Axiom proof_of_solver_safety_wit_100 : solver_safety_wit_100.
Axiom proof_of_solver_safety_wit_101 : solver_safety_wit_101.
Axiom proof_of_solver_safety_wit_102 : solver_safety_wit_102.
Axiom proof_of_solver_safety_wit_103 : solver_safety_wit_103.
Axiom proof_of_solver_safety_wit_104 : solver_safety_wit_104.
Axiom proof_of_solver_safety_wit_105 : solver_safety_wit_105.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Axiom proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Axiom proof_of_solver_entail_wit_8_3 : solver_entail_wit_8_3.
Axiom proof_of_solver_entail_wit_8_4 : solver_entail_wit_8_4.
Axiom proof_of_solver_entail_wit_8_5 : solver_entail_wit_8_5.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Axiom proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Axiom proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Axiom proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Axiom proof_of_solver_entail_wit_13_3 : solver_entail_wit_13_3.
Axiom proof_of_solver_entail_wit_13_4 : solver_entail_wit_13_4.
Axiom proof_of_solver_entail_wit_13_5 : solver_entail_wit_13_5.
Axiom proof_of_solver_entail_wit_13_6 : solver_entail_wit_13_6.
Axiom proof_of_solver_entail_wit_13_7 : solver_entail_wit_13_7.
Axiom proof_of_solver_entail_wit_13_8 : solver_entail_wit_13_8.
Axiom proof_of_solver_entail_wit_13_9 : solver_entail_wit_13_9.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Axiom proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Axiom proof_of_solver_entail_wit_16_1 : solver_entail_wit_16_1.
Axiom proof_of_solver_entail_wit_16_2 : solver_entail_wit_16_2.
Axiom proof_of_solver_entail_wit_17 : solver_entail_wit_17.
Axiom proof_of_solver_entail_wit_18 : solver_entail_wit_18.
Axiom proof_of_solver_entail_wit_19_1 : solver_entail_wit_19_1.
Axiom proof_of_solver_entail_wit_19_2 : solver_entail_wit_19_2.
Axiom proof_of_solver_entail_wit_19_3 : solver_entail_wit_19_3.
Axiom proof_of_solver_entail_wit_19_4 : solver_entail_wit_19_4.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
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
Axiom proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19_pure : solver_partial_solve_wit_19_pure.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20_pure : solver_partial_solve_wit_20_pure.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24_pure : solver_partial_solve_wit_24_pure.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.

End VC_Correct.
