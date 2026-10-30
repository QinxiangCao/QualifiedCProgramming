From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P045_959C_mahmoud_and_ehab_and_the_wrong_algorithm_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (6 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 6) ”
.

Definition solver_safety_wit_2 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre < 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg eu_pre 1 (n_pre - 1 ) )
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_6 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (IntArray.undef_seg ev_pre 1 (n_pre - 1 ) )
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg eu_pre 1 (n_pre - 1 ) )
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (IntArray.undef_seg ev_pre 1 (n_pre - 1 ) )
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg eu_pre 1 (n_pre - 1 ) )
  **  ((( &( "m" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg eu_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (IntArray.undef_seg ev_pre 1 (n_pre - 1 ) )
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_9 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (IntArray.undef_seg eu_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (((0 + 1 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((0 + 1 ) + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (IntArray.undef_seg eu_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> ((0 + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg eu_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg ev_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> ((0 + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (4 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_12 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (IntArray.undef_seg eu_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> ((0 + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ ((((0 + 1 ) + 1 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((0 + 1 ) + 1 ) + 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (IntArray.undef_seg eu_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> (((0 + 1 ) + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_14 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg eu_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (IntArray.undef_seg ev_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> (((0 + 1 ) + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (5 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 5) ”
.

Definition solver_safety_wit_15 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (IntArray.undef_seg eu_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> (((0 + 1 ) + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (((((0 + 1 ) + 1 ) + 1 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((((0 + 1 ) + 1 ) + 1 ) + 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (IntArray.undef_seg eu_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> ((((0 + 1 ) + 1 ) + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_17 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg eu_pre ((((1 + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (IntArray.undef_seg ev_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> ((((0 + 1 ) + 1 ) + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (6 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 6) ”
.

Definition solver_safety_wit_18 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre ((((1 + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 6)
  **  (IntArray.undef_seg eu_pre ((((1 + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> ((((0 + 1 ) + 1 ) + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ ((((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.undef_seg ev_pre ((((1 + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 6)
  **  (IntArray.undef_seg eu_pre ((((1 + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
|--
  “ (7 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 7) ”
.

Definition solver_safety_wit_20 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (vs: (@list Z)) (us: (@list Z)) (m: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us)) = m)) (PreH8 : ((Zlength (vs)) = m)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 ))))),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.seg eu_pre 0 m us )
  **  (IntArray.undef_seg eu_pre m (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 m vs )
  **  (IntArray.undef_seg ev_pre m (n_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (vs: (@list Z)) (us: (@list Z)) (m: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us)) = m)) (PreH8 : ((Zlength (vs)) = m)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 ))))),
  (IntArray.seg ev_pre 0 (m + 1 ) (app (vs) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (m + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (m + 1 ) (app (us) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (m + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "m" ) )) # Int  |-> m)
|--
  “ ((m + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (m + 1 )) ”
.

Definition solver_safety_wit_22 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (vs: (@list Z)) (us: (@list Z)) (m: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us)) = m)) (PreH8 : ((Zlength (vs)) = m)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 ))))),
  (IntArray.seg ev_pre 0 (m + 1 ) (app (vs) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (m + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (m + 1 ) (app (us) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (m + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
|--
  “ ((v + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_23 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (vs: (@list Z)) (us: (@list Z)) (m: Z) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us)) = m)) (PreH8 : ((Zlength (vs)) = m)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 ))))),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.seg eu_pre 0 m us )
  **  (IntArray.undef_seg eu_pre m (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 m vs )
  **  (IntArray.undef_seg ev_pre m (n_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre ((((1 + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 6)
  **  (IntArray.undef_seg eu_pre ((((1 + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  EX (vs: (@list Z)) (us: (@list Z)),
  “ (6 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (7 <= 7) ”
  &&  “ (7 <= (n_pre + 1 )) ”
  &&  “ ((((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) = (7 - 2 )) ”
  &&  “ ((Zlength (us)) = (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 )) ”
  &&  “ ((Zlength (vs)) = (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ))) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 )))) ”
  &&  (IntArray.seg eu_pre 0 (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) us )
  **  (IntArray.undef_seg eu_pre (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) vs )
  **  (IntArray.undef_seg ev_pre (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
) \/
(
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (3 <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (4 <= INT_MAX)) (PreH4 : (5 <= INT_MAX)) (PreH5 : (2 <= INT_MAX)) (PreH6 : (6 <= INT_MAX)) (PreH7 : (3 >= INT_MIN)) (PreH8 : (1 >= INT_MIN)) (PreH9 : (4 >= INT_MIN)) (PreH10 : (5 >= INT_MIN)) (PreH11 : (2 >= INT_MIN)) (PreH12 : (6 >= INT_MIN)) (PreH13 : (n_pre >= 6)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 100000)),
  (((ev_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 6)
  **  (((eu_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  EX (vs: (@list Z)) (us: (@list Z)),
  “ (6 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (7 <= 7) ”
  &&  “ (7 <= (n_pre + 1 )) ”
  &&  “ ((((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) = (7 - 2 )) ”
  &&  “ ((Zlength (us)) = (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 )) ”
  &&  “ ((Zlength (vs)) = (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ))) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 )))) ”
  &&  (IntArray.seg eu_pre 0 (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) us )
  **  (IntArray.seg ev_pre 0 (((((0 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) vs )
).

Definition solver_entail_wit_2 :=
(
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (vs_2: (@list Z)) (us_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us_2)) = m)) (PreH8 : ((Zlength (vs_2)) = m)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us_2 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us_2 0) = 1))) /\ ((Znth i vs_2 0) = (i + 2 ))))),
  (IntArray.seg ev_pre 0 (m + 1 ) (app (vs_2) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (m + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (m + 1 ) (app (us_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (m + 1 ) (n_pre - 1 ) )
|--
  EX (vs: (@list Z)) (us: (@list Z)),
  “ (6 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (7 <= (v + 1 )) ”
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ”
  &&  “ ((m + 1 ) = ((v + 1 ) - 2 )) ”
  &&  “ ((Zlength (us)) = (m + 1 )) ”
  &&  “ ((Zlength (vs)) = (m + 1 )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (m + 1 ))) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 )))) ”
  &&  (IntArray.seg eu_pre 0 (m + 1 ) us )
  **  (IntArray.undef_seg eu_pre (m + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 (m + 1 ) vs )
  **  (IntArray.undef_seg ev_pre (m + 1 ) (n_pre - 1 ) )
) \/
(
forall (n_pre: Z) (vs_2: (@list Z)) (us_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us_2)) = m)) (PreH8 : ((Zlength (vs_2)) = m)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us_2 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us_2 0) = 1))) /\ ((Znth i vs_2 0) = (i + 2 ))))),
  TT && emp 
|--
  “ ((Zlength ((app (vs_2) ((cons (v) ((@nil Z))))))) = ((v - 2 ) + 1 )) ”
  &&  “ ((Zlength ((app (us_2) ((cons (1) ((@nil Z))))))) = ((v - 2 ) + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (n_pre: Z) (vs_2: (@list Z)) (us_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us_2)) = m)) (PreH8 : ((Zlength (vs_2)) = m)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us_2 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us_2 0) = 1))) /\ ((Znth i vs_2 0) = (i + 2 ))))),
  ((Zlength ((app (vs_2) ((cons (v) ((@nil Z))))))) = ((v - 2 ) + 1 ))
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (n_pre: Z) (vs_2: (@list Z)) (us_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us_2)) = m)) (PreH8 : ((Zlength (vs_2)) = m)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us_2 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us_2 0) = 1))) /\ ((Znth i vs_2 0) = (i + 2 ))))),
  ((Zlength ((app (us_2) ((cons (1) ((@nil Z))))))) = ((v - 2 ) + 1 ))
.

Definition solver_return_wit_1 :=
(
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (vs_2: (@list Z)) (us_2: (@list Z)) (m: Z) (v: Z) __default__Prod_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us_2)) = m)) (PreH8 : ((Zlength (vs_2)) = m)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m)) -> (((((i_2 = 3) \/ (i_2 = 4)) -> ((Znth i_2 us_2 0) = 2)) /\ (((i_2 <> 3) /\ (i_2 <> 4)) -> ((Znth i_2 us_2 0) = 1))) /\ ((Znth i_2 vs_2 0) = (i_2 + 2 ))))),
  (IntArray.seg eu_pre 0 m us_2 )
  **  (IntArray.undef_seg eu_pre m (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 m vs_2 )
  **  (IntArray.undef_seg ev_pre m (n_pre - 1 ) )
|--
  EX (vs: (@list Z)) (us: (@list Z)) (edges: (@list (Z * Z))) (out: ((@option (@list (Z * Z))) * (@option (@list (Z * Z))))),
  “ (Spec n_pre out ) ”
  &&  “ ((fst (out)) = (Some (edges))) ”
  &&  “ (1 = 1) ”
  &&  “ ((Zlength (edges)) = (n_pre - 1 )) ”
  &&  “ ((Zlength (us)) = (n_pre - 1 )) ”
  &&  “ ((Zlength (vs)) = (n_pre - 1 )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (n_pre - 1 ))) -> (((Znth i us 0) = (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((Znth i vs 0) = (snd ((Znth i edges __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full eu_pre (n_pre - 1 ) us )
  **  (IntArray.full ev_pre (n_pre - 1 ) vs )
) \/
(
forall (n_pre: Z) (vs_2: (@list Z)) (us_2: (@list Z)) (m: Z) (v: Z) __default__Prod_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us_2)) = m)) (PreH8 : ((Zlength (vs_2)) = m)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m)) -> (((((i_2 = 3) \/ (i_2 = 4)) -> ((Znth i_2 us_2 0) = 2)) /\ (((i_2 <> 3) /\ (i_2 <> 4)) -> ((Znth i_2 us_2 0) = 1))) /\ ((Znth i_2 vs_2 0) = (i_2 + 2 ))))),
  TT && emp 
|--
  EX (edges: (@list (Z * Z))) (out: ((@option (@list (Z * Z))) * (@option (@list (Z * Z))))),
  “ (Spec n_pre out ) ”
  &&  “ ((fst (out)) = (Some (edges))) ”
  &&  “ ((Zlength (edges)) = (n_pre - 1 )) ”
  &&  “ ((Zlength (us_2)) = (n_pre - 1 )) ”
  &&  “ ((Zlength (vs_2)) = (n_pre - 1 )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (n_pre - 1 ))) -> (((Znth i us_2 0) = (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((Znth i vs_2 0) = (snd ((Znth i edges __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_return_wit_2 :=
(
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre < 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  EX (out: ((@option (@list (Z * Z))) * (@option (@list (Z * Z))))),
  “ (Spec n_pre out ) ”
  &&  “ ((fst (out)) = None) ”
  &&  “ (0 = 0) ”
  &&  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
) \/
(
forall (n_pre: Z) (PreH1 : (n_pre < 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  TT && emp 
|--
  EX (out: ((@option (@list (Z * Z))) * (@option (@list (Z * Z))))),
  “ (Spec n_pre out ) ”
  &&  “ ((fst (out)) = None) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (n_pre >= 6) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  (((eu_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg eu_pre 1 (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
.

Definition solver_partial_solve_wit_2 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg eu_pre 1 (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (n_pre >= 6) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  (((ev_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ev_pre 1 (n_pre - 1 ) )
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg eu_pre 1 (n_pre - 1 ) )
.

Definition solver_partial_solve_wit_3 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (IntArray.undef_seg ev_pre 1 (n_pre - 1 ) )
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg eu_pre 1 (n_pre - 1 ) )
|--
  “ (n_pre >= 6) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i eu_pre (0 + 1 ) 1 (n_pre - 1 ) )
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (IntArray.undef_seg ev_pre 1 (n_pre - 1 ) )
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
.

Definition solver_partial_solve_wit_4 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg eu_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (IntArray.undef_seg ev_pre 1 (n_pre - 1 ) )
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  “ (n_pre >= 6) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i ev_pre (0 + 1 ) 1 (n_pre - 1 ) )
  **  (IntArray.undef_seg eu_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
.

Definition solver_partial_solve_wit_5 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (IntArray.undef_seg eu_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  “ (n_pre >= 6) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i eu_pre ((0 + 1 ) + 1 ) (1 + 1 ) (n_pre - 1 ) )
  **  (IntArray.undef_seg ev_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
.

Definition solver_partial_solve_wit_6 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg eu_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg ev_pre (1 + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  “ (n_pre >= 6) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i ev_pre ((0 + 1 ) + 1 ) (1 + 1 ) (n_pre - 1 ) )
  **  (IntArray.undef_seg eu_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
.

Definition solver_partial_solve_wit_7 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (IntArray.undef_seg eu_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  “ (n_pre >= 6) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i eu_pre (((0 + 1 ) + 1 ) + 1 ) ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (IntArray.undef_seg ev_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
.

Definition solver_partial_solve_wit_8 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg eu_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (IntArray.undef_seg ev_pre ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  “ (n_pre >= 6) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i ev_pre (((0 + 1 ) + 1 ) + 1 ) ((1 + 1 ) + 1 ) (n_pre - 1 ) )
  **  (IntArray.undef_seg eu_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
.

Definition solver_partial_solve_wit_9 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg ev_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (IntArray.undef_seg eu_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  “ (n_pre >= 6) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  (((eu_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i eu_pre ((((0 + 1 ) + 1 ) + 1 ) + 1 ) (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (IntArray.undef_seg ev_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
.

Definition solver_partial_solve_wit_10 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (PreH1 : (n_pre >= 6)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)),
  (IntArray.undef_seg eu_pre ((((1 + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (IntArray.undef_seg ev_pre (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  “ (n_pre >= 6) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  (((ev_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i ev_pre ((((0 + 1 ) + 1 ) + 1 ) + 1 ) (((1 + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (IntArray.undef_seg eu_pre ((((1 + 1 ) + 1 ) + 1 ) + 1 ) (n_pre - 1 ) )
  **  (((eu_pre + (((((0 + 1 ) + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 5)
  **  (((eu_pre + ((((0 + 1 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 2)
  **  (((ev_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 4)
  **  (((eu_pre + (((0 + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 3)
  **  (((eu_pre + ((0 + 1 ) * sizeof(INT)))) # Int  |-> 1)
  **  (((ev_pre + (0 * sizeof(INT)))) # Int  |-> 2)
  **  (((eu_pre + (0 * sizeof(INT)))) # Int  |-> 1)
.

Definition solver_partial_solve_wit_11 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (vs: (@list Z)) (us: (@list Z)) (m: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us)) = m)) (PreH8 : ((Zlength (vs)) = m)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 ))))),
  (IntArray.seg eu_pre 0 m us )
  **  (IntArray.undef_seg eu_pre m (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 m vs )
  **  (IntArray.undef_seg ev_pre m (n_pre - 1 ) )
|--
  “ (v <= n_pre) ”
  &&  “ (6 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (7 <= v) ”
  &&  “ (v <= (n_pre + 1 )) ”
  &&  “ (m = (v - 2 )) ”
  &&  “ ((Zlength (us)) = m) ”
  &&  “ ((Zlength (vs)) = m) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 )))) ”
  &&  (((eu_pre + (m * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg eu_pre (m + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 m us )
  **  (IntArray.seg ev_pre 0 m vs )
  **  (IntArray.undef_seg ev_pre m (n_pre - 1 ) )
.

Definition solver_partial_solve_wit_12 :=
forall (n_pre: Z) (eu_pre: Z) (ev_pre: Z) (vs: (@list Z)) (us: (@list Z)) (m: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (6 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (7 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (m = (v - 2 ))) (PreH7 : ((Zlength (us)) = m)) (PreH8 : ((Zlength (vs)) = m)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 ))))),
  (IntArray.seg eu_pre 0 (m + 1 ) (app (us) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (m + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 m vs )
  **  (IntArray.undef_seg ev_pre m (n_pre - 1 ) )
|--
  “ (v <= n_pre) ”
  &&  “ (6 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (7 <= v) ”
  &&  “ (v <= (n_pre + 1 )) ”
  &&  “ (m = (v - 2 )) ”
  &&  “ ((Zlength (us)) = m) ”
  &&  “ ((Zlength (vs)) = m) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m)) -> (((((i = 3) \/ (i = 4)) -> ((Znth i us 0) = 2)) /\ (((i <> 3) /\ (i <> 4)) -> ((Znth i us 0) = 1))) /\ ((Znth i vs 0) = (i + 2 )))) ”
  &&  (((ev_pre + (m * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ev_pre (m + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (m + 1 ) (app (us) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (m + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 m vs )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
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
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.

End VC_Correct.
