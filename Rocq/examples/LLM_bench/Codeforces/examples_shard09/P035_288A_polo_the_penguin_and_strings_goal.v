From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P035_288A_polo_the_penguin_and_strings_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre <= n_pre)) (PreH2 : (1 <= length)) (PreH3 : (length <= 1000000)) (PreH4 : (1 <= alphabet_size)) (PreH5 : (alphabet_size <= 26)) (PreH6 : (n_pre = length)) (PreH7 : (k_pre = alphabet_size)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= length)) (PreH4 : (length <= 1000000)) (PreH5 : (1 <= alphabet_size)) (PreH6 : (alphabet_size <= 26)) (PreH7 : (n_pre = length)) (PreH8 : (k_pre = alphabet_size)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre > n_pre)) (PreH2 : (1 <= length)) (PreH3 : (length <= 1000000)) (PreH4 : (1 <= alphabet_size)) (PreH5 : (alphabet_size <= 26)) (PreH6 : (n_pre = length)) (PreH7 : (k_pre = alphabet_size)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (n_pre > 1)) (PreH2 : (k_pre = 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (n_pre <= 1)) (PreH2 : (k_pre = 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre <> 1)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= length)) (PreH4 : (length <= 1000000)) (PreH5 : (1 <= alphabet_size)) (PreH6 : (alphabet_size <= 26)) (PreH7 : (n_pre = length)) (PreH8 : (k_pre = alphabet_size)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre <> 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ False ”
.

Definition solver_safety_wit_8 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (k_pre <> 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ False ”
.

Definition solver_safety_wit_9 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_11 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 97)
  **  (CharArray.undef_seg out_pre 1 (n_pre + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 97)
  **  (CharArray.undef_seg out_pre 1 (n_pre + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (n_pre = 1)) (PreH2 : (k_pre = 1)) (PreH3 : (n_pre = length)) (PreH4 : (k_pre = alphabet_size)) (PreH5 : (Spec n_pre k_pre (Some ((PoloCandidate (n_pre) (k_pre)))) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre (n_pre + 1 ) (app ((PoloCandidate (n_pre) (k_pre))) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre <> 1)) (PreH2 : (k_pre <> 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  ((( &( "alt" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ ((n_pre - (k_pre - 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - (k_pre - 2 ) )) ”
.

Definition solver_safety_wit_15 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre <> 1)) (PreH2 : (k_pre <> 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  ((( &( "alt" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ ((k_pre - 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k_pre - 2 )) ”
.

Definition solver_safety_wit_16 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre <> 1)) (PreH2 : (k_pre <> 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  ((( &( "alt" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_17 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre <> 1)) (PreH2 : (k_pre <> 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "alt" ) )) # Int  |-> (n_pre - (k_pre - 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  (CharArray.full out_pre (i + 1 ) (app ((AlternatingPrefix (i))) ((cons ((signed_last_nbits ((97 + (i % ( 2 ) ) )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (i + 1 ) (n_pre + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_19 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre i (AlternatingPrefix (i)) )
  **  (CharArray.undef_seg out_pre i (n_pre + 1 ) )
|--
  “ ((97 + (i % ( 2 ) ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (97 + (i % ( 2 ) ) )) ”
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre i (AlternatingPrefix (i)) )
  **  (CharArray.undef_seg out_pre i (n_pre + 1 ) )
|--
  “ ((97 + (i % ( 2 ) ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (97 + (i % ( 2 ) ) )) ”
).

Definition solver_safety_wit_19_split_goal_1 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre i (AlternatingPrefix (i)) )
  **  (CharArray.undef_seg out_pre i (n_pre + 1 ) )
|--
  “ ((97 + (i % ( 2 ) ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre i (AlternatingPrefix (i)) )
  **  (CharArray.undef_seg out_pre i (n_pre + 1 ) )
|--
  “ ((INT_MIN) <= (97 + (i % ( 2 ) ) )) ”
.

Definition solver_safety_wit_20 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre i (AlternatingPrefix (i)) )
  **  (CharArray.undef_seg out_pre i (n_pre + 1 ) )
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_21 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre i (AlternatingPrefix (i)) )
  **  (CharArray.undef_seg out_pre i (n_pre + 1 ) )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_22 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre i (AlternatingPrefix (i)) )
  **  (CharArray.undef_seg out_pre i (n_pre + 1 ) )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_23 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i >= alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  (CharArray.full out_pre i (AlternatingPrefix (i)) )
  **  (CharArray.undef_seg out_pre i (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (n_pre = length)) (PreH2 : (k_pre = alphabet_size)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 26)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH9 : (2 <= alt)) (PreH10 : (alt <= n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (k_pre - 2 ))),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre (alt + i ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (i)))) )
  **  (CharArray.undef_seg out_pre (alt + i ) (n_pre + 1 ) )
|--
  “ ((k_pre - 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k_pre - 2 )) ”
.

Definition solver_safety_wit_25 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (n_pre = length)) (PreH2 : (k_pre = alphabet_size)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 26)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH9 : (2 <= alt)) (PreH10 : (alt <= n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (k_pre - 2 ))),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre (alt + i ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (i)))) )
  **  (CharArray.undef_seg out_pre (alt + i ) (n_pre + 1 ) )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_26 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  (CharArray.full out_pre ((alt + i ) + 1 ) (app ((app ((AlternatingPrefix (alt))) ((IncreasingTail (i))))) ((cons ((99 + i )) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((alt + i ) + 1 ) (n_pre + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_27 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre (alt + i ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (i)))) )
  **  (CharArray.undef_seg out_pre (alt + i ) (n_pre + 1 ) )
|--
  “ ((alt + i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (alt + i )) ”
.

Definition solver_safety_wit_28 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre (alt + i ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (i)))) )
  **  (CharArray.undef_seg out_pre (alt + i ) (n_pre + 1 ) )
|--
  “ ((99 + i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (99 + i )) ”
.

Definition solver_safety_wit_29 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre (alt + i ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (i)))) )
  **  (CharArray.undef_seg out_pre (alt + i ) (n_pre + 1 ) )
|--
  “ (99 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 99) ”
.

Definition solver_safety_wit_30 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i >= (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  (CharArray.full out_pre (alt + i ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (i)))) )
  **  (CharArray.undef_seg out_pre (alt + i ) (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_31 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (alt: Z) (PreH1 : (n_pre = length)) (PreH2 : (k_pre = alphabet_size)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 26)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH9 : (Spec n_pre k_pre (Some ((PoloCandidate (n_pre) (k_pre)))) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "alt" ) )) # Int  |-> alt)
  **  (CharArray.full out_pre (n_pre + 1 ) (app ((PoloCandidate (n_pre) (k_pre))) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  (((out_pre + (1 * sizeof(CHAR)))) # Char  |-> 0)
  **  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 97)
|--
  “ (n_pre = 1) ”
  &&  “ (k_pre = 1) ”
  &&  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (Spec n_pre k_pre (Some ((PoloCandidate (n_pre) (k_pre)))) ) ”
  &&  (CharArray.full out_pre (n_pre + 1 ) (app ((PoloCandidate (n_pre) (k_pre))) ((cons (0) ((@nil Z))))) )
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  (((out_pre + (1 * sizeof(CHAR)))) # Char  |-> 0)
  **  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 97)
|--
  “ (Spec length 1 (Some ((PoloCandidate (length) (1)))) ) ”
  &&  (CharArray.full out_pre (n_pre + 1 ) (app ((PoloCandidate (n_pre) (k_pre))) ((cons (0) ((@nil Z))))) )
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  (((out_pre + (1 * sizeof(CHAR)))) # Char  |-> 0)
  **  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 97)
|--
  “ (Spec length 1 (Some ((PoloCandidate (length) (1)))) ) ”
.

Definition solver_entail_wit_1_split_goal_spatial :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  (((out_pre + (1 * sizeof(CHAR)))) # Char  |-> 0)
  **  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 97)
|--
  (CharArray.full out_pre (n_pre + 1 ) (app ((PoloCandidate (n_pre) (k_pre))) ((cons (0) ((@nil Z))))) )
.

Definition solver_entail_wit_2 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre <> 1)) (PreH2 : (k_pre <> 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= 26) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ ((n_pre - (k_pre - 2 ) ) = (n_pre - (k_pre - 2 ) )) ”
  &&  “ (2 <= (n_pre - (k_pre - 2 ) )) ”
  &&  “ ((n_pre - (k_pre - 2 ) ) <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (n_pre - (k_pre - 2 ) )) ”
  &&  (CharArray.full out_pre 0 (AlternatingPrefix (0)) )
  **  (CharArray.undef_seg out_pre 0 (n_pre + 1 ) )
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre <> 1)) (PreH2 : (k_pre <> 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  TT && emp 
|--
  “ ((AlternatingPrefix (0)) = (@nil Z)) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre <> 1)) (PreH2 : (k_pre <> 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  ((AlternatingPrefix (0)) = (@nil Z))
.

Definition solver_entail_wit_3 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  (CharArray.full out_pre (i + 1 ) (app ((AlternatingPrefix (i))) ((cons ((signed_last_nbits ((97 + (i % ( 2 ) ) )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= 26) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (alt = (n_pre - (k_pre - 2 ) )) ”
  &&  “ (2 <= alt) ”
  &&  “ (alt <= n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= alt) ”
  &&  (CharArray.full out_pre (i + 1 ) (AlternatingPrefix ((i + 1 ))) )
  **  (CharArray.undef_seg out_pre (i + 1 ) (n_pre + 1 ) )
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  TT && emp 
|--
  “ ((app ((AlternatingPrefix (i))) ((cons ((signed_last_nbits ((97 + (i % ( 2 ) ) )) (8))) ((@nil Z))))) = (AlternatingPrefix ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  ((app ((AlternatingPrefix (i))) ((cons ((signed_last_nbits ((97 + (i % ( 2 ) ) )) (8))) ((@nil Z))))) = (AlternatingPrefix ((i + 1 ))))
.

Definition solver_entail_wit_4 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i >= alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  (CharArray.full out_pre i (AlternatingPrefix (i)) )
  **  (CharArray.undef_seg out_pre i (n_pre + 1 ) )
|--
  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= 26) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (alt = (n_pre - (k_pre - 2 ) )) ”
  &&  “ (2 <= alt) ”
  &&  “ (alt <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (k_pre - 2 )) ”
  &&  (CharArray.full out_pre (alt + 0 ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (0)))) )
  **  (CharArray.undef_seg out_pre (alt + 0 ) (n_pre + 1 ) )
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i >= alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  (CharArray.full out_pre i (AlternatingPrefix (i)) )
|--
  (CharArray.full out_pre (alt + 0 ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (0)))) )
).

Definition solver_entail_wit_4_split_goal_spatial :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i >= alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  (CharArray.full out_pre i (AlternatingPrefix (i)) )
|--
  (CharArray.full out_pre (alt + 0 ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (0)))) )
.

Definition solver_entail_wit_5 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  (CharArray.full out_pre ((alt + i ) + 1 ) (app ((app ((AlternatingPrefix (alt))) ((IncreasingTail (i))))) ((cons ((99 + i )) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((alt + i ) + 1 ) (n_pre + 1 ) )
|--
  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= 26) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (alt = (n_pre - (k_pre - 2 ) )) ”
  &&  “ (2 <= alt) ”
  &&  “ (alt <= n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (k_pre - 2 )) ”
  &&  (CharArray.full out_pre (alt + (i + 1 ) ) (app ((AlternatingPrefix (alt))) ((IncreasingTail ((i + 1 ))))) )
  **  (CharArray.undef_seg out_pre (alt + (i + 1 ) ) (n_pre + 1 ) )
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  (CharArray.full out_pre ((alt + i ) + 1 ) (app ((app ((AlternatingPrefix (alt))) ((IncreasingTail (i))))) ((cons ((99 + i )) ((@nil Z))))) )
|--
  (CharArray.full out_pre (alt + (i + 1 ) ) (app ((AlternatingPrefix (alt))) ((IncreasingTail ((i + 1 ))))) )
).

Definition solver_entail_wit_5_split_goal_spatial :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  (CharArray.full out_pre ((alt + i ) + 1 ) (app ((app ((AlternatingPrefix (alt))) ((IncreasingTail (i))))) ((cons ((99 + i )) ((@nil Z))))) )
|--
  (CharArray.full out_pre (alt + (i + 1 ) ) (app ((AlternatingPrefix (alt))) ((IncreasingTail ((i + 1 ))))) )
.

Definition solver_entail_wit_6 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i >= (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  (CharArray.full out_pre ((alt + i ) + 1 ) (app ((app ((AlternatingPrefix (alt))) ((IncreasingTail (i))))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((alt + i ) + 1 ) (n_pre + 1 ) )
|--
  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= 26) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (alt = (n_pre - (k_pre - 2 ) )) ”
  &&  “ (Spec n_pre k_pre (Some ((PoloCandidate (n_pre) (k_pre)))) ) ”
  &&  (CharArray.full out_pre (n_pre + 1 ) (app ((PoloCandidate (n_pre) (k_pre))) ((cons (0) ((@nil Z))))) )
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i >= (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  (CharArray.full out_pre ((alt + i ) + 1 ) (app ((app ((AlternatingPrefix (alt))) ((IncreasingTail (i))))) ((cons (0) ((@nil Z))))) )
|--
  “ (Spec length alphabet_size (Some ((PoloCandidate (length) (alphabet_size)))) ) ”
  &&  (CharArray.full out_pre (n_pre + 1 ) (app ((PoloCandidate (n_pre) (k_pre))) ((cons (0) ((@nil Z))))) )
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i >= (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  (CharArray.full out_pre ((alt + i ) + 1 ) (app ((app ((AlternatingPrefix (alt))) ((IncreasingTail (i))))) ((cons (0) ((@nil Z))))) )
|--
  “ (Spec length alphabet_size (Some ((PoloCandidate (length) (alphabet_size)))) ) ”
.

Definition solver_entail_wit_6_split_goal_spatial :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i >= (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  (CharArray.full out_pre ((alt + i ) + 1 ) (app ((app ((AlternatingPrefix (alt))) ((IncreasingTail (i))))) ((cons (0) ((@nil Z))))) )
|--
  (CharArray.full out_pre (n_pre + 1 ) (app ((PoloCandidate (n_pre) (k_pre))) ((cons (0) ((@nil Z))))) )
.

Definition solver_return_wit_1 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (alt: Z) (PreH1 : (n_pre = length)) (PreH2 : (k_pre = alphabet_size)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 26)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH9 : (Spec n_pre k_pre (Some ((PoloCandidate (n_pre) (k_pre)))) )),
  (CharArray.full out_pre (n_pre + 1 ) (app ((PoloCandidate (n_pre) (k_pre))) ((cons (0) ((@nil Z))))) )
|--
  EX (xs: (@list Z)) (out_spec: (@option (@list Z))),
  “ (Spec length alphabet_size out_spec ) ”
  &&  “ (P035ReturnBridge out_spec 1 ) ”
  &&  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (out_spec = (Some (xs))) ”
  &&  “ (1 = 1) ”
  &&  “ ((Zlength (xs)) = n_pre) ”
  &&  (CharArray.full out_pre (n_pre + 1 ) (app (xs) ((cons (0) ((@nil Z))))) )
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (alt: Z) (PreH1 : (n_pre = length)) (PreH2 : (k_pre = alphabet_size)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 26)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH9 : (Spec n_pre k_pre (Some ((PoloCandidate (n_pre) (k_pre)))) )),
  TT && emp 
|--
  EX (xs: (@list Z)),
  “ ((app ((PoloCandidate (length) (alphabet_size))) ((cons (0) ((@nil Z))))) = (app (xs) ((cons (0) ((@nil Z)))))) ”
  &&  “ (Spec length alphabet_size (Some (xs)) ) ”
  &&  “ (P035ReturnBridge (Some (xs)) 1 ) ”
  &&  “ ((Zlength (xs)) = length) ”
  &&  emp
).

Definition solver_return_wit_2 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (n_pre = 1)) (PreH2 : (k_pre = 1)) (PreH3 : (n_pre = length)) (PreH4 : (k_pre = alphabet_size)) (PreH5 : (Spec n_pre k_pre (Some ((PoloCandidate (n_pre) (k_pre)))) )),
  (CharArray.full out_pre (n_pre + 1 ) (app ((PoloCandidate (n_pre) (k_pre))) ((cons (0) ((@nil Z))))) )
|--
  EX (xs: (@list Z)) (out_spec: (@option (@list Z))),
  “ (Spec length alphabet_size out_spec ) ”
  &&  “ (P035ReturnBridge out_spec 1 ) ”
  &&  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (out_spec = (Some (xs))) ”
  &&  “ (1 = 1) ”
  &&  “ ((Zlength (xs)) = n_pre) ”
  &&  (CharArray.full out_pre (n_pre + 1 ) (app (xs) ((cons (0) ((@nil Z))))) )
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (n_pre = 1)) (PreH2 : (k_pre = 1)) (PreH3 : (n_pre = length)) (PreH4 : (k_pre = alphabet_size)) (PreH5 : (Spec n_pre k_pre (Some ((PoloCandidate (n_pre) (k_pre)))) )),
  TT && emp 
|--
  EX (xs: (@list Z)),
  “ ((app ((PoloCandidate (1) (1))) ((cons (0) ((@nil Z))))) = (app (xs) ((cons (0) ((@nil Z)))))) ”
  &&  “ (Spec length alphabet_size (Some (xs)) ) ”
  &&  “ (P035ReturnBridge (Some (xs)) 1 ) ”
  &&  “ ((Zlength (xs)) = 1) ”
  &&  emp
).

Definition solver_return_wit_3 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre > n_pre)) (PreH2 : (1 <= length)) (PreH3 : (length <= 1000000)) (PreH4 : (1 <= alphabet_size)) (PreH5 : (alphabet_size <= 26)) (PreH6 : (n_pre = length)) (PreH7 : (k_pre = alphabet_size)),
  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  EX (out_spec: (@option (@list Z))),
  “ (Spec length alphabet_size out_spec ) ”
  &&  “ (P035ReturnBridge out_spec 0 ) ”
  &&  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (out_spec = None) ”
  &&  “ (0 = 0) ”
  &&  (CharArray.undef_full out_pre (n_pre + 1 ) )
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre > n_pre)) (PreH2 : (1 <= length)) (PreH3 : (length <= 1000000)) (PreH4 : (1 <= alphabet_size)) (PreH5 : (alphabet_size <= 26)) (PreH6 : (n_pre = length)) (PreH7 : (k_pre = alphabet_size)),
  TT && emp 
|--
  “ (P035ReturnBridge None 0 ) ”
  &&  “ (Spec length alphabet_size None ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre > n_pre)) (PreH2 : (1 <= length)) (PreH3 : (length <= 1000000)) (PreH4 : (1 <= alphabet_size)) (PreH5 : (alphabet_size <= 26)) (PreH6 : (n_pre = length)) (PreH7 : (k_pre = alphabet_size)),
  (P035ReturnBridge None 0 )
.

Definition solver_return_wit_3_split_goal_2 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre > n_pre)) (PreH2 : (1 <= length)) (PreH3 : (length <= 1000000)) (PreH4 : (1 <= alphabet_size)) (PreH5 : (alphabet_size <= 26)) (PreH6 : (n_pre = length)) (PreH7 : (k_pre = alphabet_size)),
  (Spec length alphabet_size None )
.

Definition solver_return_wit_4 :=
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (n_pre > 1)) (PreH2 : (k_pre = 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  EX (out_spec: (@option (@list Z))),
  “ (Spec length alphabet_size out_spec ) ”
  &&  “ (P035ReturnBridge out_spec 0 ) ”
  &&  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (out_spec = None) ”
  &&  “ (0 = 0) ”
  &&  (CharArray.undef_full out_pre (n_pre + 1 ) )
) \/
(
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (n_pre > 1)) (PreH2 : (k_pre = 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  TT && emp 
|--
  “ (P035ReturnBridge None 0 ) ”
  &&  “ (Spec length alphabet_size None ) ”
  &&  emp
).

Definition solver_return_wit_4_split_goal_1 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (n_pre > 1)) (PreH2 : (k_pre = 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  (P035ReturnBridge None 0 )
.

Definition solver_return_wit_4_split_goal_2 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (n_pre > 1)) (PreH2 : (k_pre = 1)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= length)) (PreH5 : (length <= 1000000)) (PreH6 : (1 <= alphabet_size)) (PreH7 : (alphabet_size <= 26)) (PreH8 : (n_pre = length)) (PreH9 : (k_pre = alphabet_size)),
  (Spec length alphabet_size None )
.

Definition solver_partial_solve_wit_1 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (k_pre = 1) ”
  &&  “ (n_pre <= 1) ”
  &&  “ (k_pre = 1) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (1 <= length) ”
  &&  “ (length <= 1000000) ”
  &&  “ (1 <= alphabet_size) ”
  &&  “ (alphabet_size <= 26) ”
  &&  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  (((out_pre + (0 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg out_pre 1 (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_2 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (PreH1 : (k_pre = 1)) (PreH2 : (n_pre <= 1)) (PreH3 : (k_pre = 1)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (1 <= length)) (PreH6 : (length <= 1000000)) (PreH7 : (1 <= alphabet_size)) (PreH8 : (alphabet_size <= 26)) (PreH9 : (n_pre = length)) (PreH10 : (k_pre = alphabet_size)),
  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 97)
  **  (CharArray.undef_seg out_pre 1 (n_pre + 1 ) )
|--
  “ (k_pre = 1) ”
  &&  “ (n_pre <= 1) ”
  &&  “ (k_pre = 1) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (1 <= length) ”
  &&  “ (length <= 1000000) ”
  &&  “ (1 <= alphabet_size) ”
  &&  “ (alphabet_size <= 26) ”
  &&  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  (((out_pre + (1 * sizeof(CHAR)))) # Char  |->_)
  **  (((out_pre + (0 * sizeof(CHAR)))) # Char  |-> 97)
.

Definition solver_partial_solve_wit_3 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < alt)) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= alt)),
  (CharArray.full out_pre i (AlternatingPrefix (i)) )
  **  (CharArray.undef_seg out_pre i (n_pre + 1 ) )
|--
  “ (i < alt) ”
  &&  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= 26) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (alt = (n_pre - (k_pre - 2 ) )) ”
  &&  “ (2 <= alt) ”
  &&  “ (alt <= n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= alt) ”
  &&  (((out_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg out_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.full out_pre i (AlternatingPrefix (i)) )
.

Definition solver_partial_solve_wit_4 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i < (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  (CharArray.full out_pre (alt + i ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (i)))) )
  **  (CharArray.undef_seg out_pre (alt + i ) (n_pre + 1 ) )
|--
  “ (i < (k_pre - 2 )) ”
  &&  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= 26) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (alt = (n_pre - (k_pre - 2 ) )) ”
  &&  “ (2 <= alt) ”
  &&  “ (alt <= n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (k_pre - 2 )) ”
  &&  (((out_pre + ((alt + i ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg out_pre ((alt + i ) + 1 ) (n_pre + 1 ) )
  **  (CharArray.full out_pre (alt + i ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (i)))) )
.

Definition solver_partial_solve_wit_5 :=
forall (alphabet_size: Z) (length: Z) (n_pre: Z) (k_pre: Z) (out_pre: Z) (i: Z) (alt: Z) (PreH1 : (i >= (k_pre - 2 ))) (PreH2 : (n_pre = length)) (PreH3 : (k_pre = alphabet_size)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 26)) (PreH8 : (k_pre <= n_pre)) (PreH9 : (alt = (n_pre - (k_pre - 2 ) ))) (PreH10 : (2 <= alt)) (PreH11 : (alt <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= (k_pre - 2 ))),
  (CharArray.full out_pre (alt + i ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (i)))) )
  **  (CharArray.undef_seg out_pre (alt + i ) (n_pre + 1 ) )
|--
  “ (i >= (k_pre - 2 )) ”
  &&  “ (n_pre = length) ”
  &&  “ (k_pre = alphabet_size) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= 26) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (alt = (n_pre - (k_pre - 2 ) )) ”
  &&  “ (2 <= alt) ”
  &&  “ (alt <= n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (k_pre - 2 )) ”
  &&  (((out_pre + (n_pre * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre n_pre (alt + i ) (n_pre + 1 ) )
  **  (CharArray.full out_pre (alt + i ) (app ((AlternatingPrefix (alt))) ((IncreasingTail (i)))) )
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
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.

End VC_Correct.
