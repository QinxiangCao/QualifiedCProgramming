From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P037_1266C_diverse_matrix_lib.
Local Open Scope sac.
From SimpleC.Verification Require Import array2_strategy_goal.
From SimpleC.Verification Require Import array2_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (PreH1 : (1 <= r_pre)) (PreH2 : (r_pre <= 500)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 500)),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  (IntArray2.undef_full m_pre r_pre c_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (PreH1 : (r_pre = 1)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  (IntArray2.undef_full m_pre r_pre c_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (PreH1 : (c_pre = 1)) (PreH2 : (r_pre = 1)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 500)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 500)),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  (IntArray2.undef_full m_pre r_pre c_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (PreH1 : (ConstructionPrefix r_pre c_pre rows 0 )) (PreH2 : (r_pre <> 1)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 500)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 500)),
  (IntArray2.mixed_full m_pre r_pre c_pre rows )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (PreH1 : (ConstructionPrefix r_pre c_pre rows 0 )) (PreH2 : (c_pre <> 1)) (PreH3 : (r_pre = 1)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 500)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 500)),
  (IntArray2.mixed_full m_pre r_pre c_pre rows )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (PreH1 : (r_pre = 1)) (PreH2 : (ConstructionPrefix r_pre c_pre rows 0 )) (PreH3 : (r_pre <> 1)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 500)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 500)),
  (IntArray2.mixed_full m_pre r_pre c_pre rows )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
|--
  “ False ”
.

Definition solver_safety_wit_7 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (PreH1 : (r_pre <> 1)) (PreH2 : (ConstructionPrefix r_pre c_pre rows 0 )) (PreH3 : (c_pre <> 1)) (PreH4 : (r_pre = 1)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 500)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 500)),
  (IntArray2.mixed_full m_pre r_pre c_pre rows )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
|--
  “ False ”
.

Definition solver_safety_wit_8 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) __default__List__App_option_Z (PreH1 : (r_pre = 1)) (PreH2 : (2 <= c_pre)) (PreH3 : (c_pre <= 500)) (PreH4 : (ConstructionPrefix r_pre c_pre rows 0 )),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows (j - 1 ) )),
  (IntArray.mixed_full m_pre c_pre (replace_Znth ((j - 1 )) ((Some ((j + 1 )))) ((Znth 0 rows __default__List__App_option_Z))) )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows (j - 1 ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
|--
  “ ((j - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows (j - 1 ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows (j - 1 ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows (j - 1 ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j > c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows (j - 1 ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (PreH1 : (r_pre <> 1)) (PreH2 : (ConstructionPrefix r_pre c_pre rows 0 )) (PreH3 : (r_pre <> 1)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 500)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 500)),
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i <= r_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= (r_pre + 1 ))) (PreH8 : (0 <= ((i - 1 ) * c_pre ))) (PreH9 : (((i - 1 ) * c_pre ) <= (r_pre * c_pre ))) (PreH10 : ((r_pre * c_pre ) <= 250000)) (PreH11 : (ConstructionPrefix r_pre c_pre rows ((i - 1 ) * c_pre ) )),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j > c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  (((m_pre + ((((i - 1 ) * c_pre ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> ((c_pre + i ) * j ))
  **  (IntArray.mixed_missing_i (m_pre + (((i - 1 ) * c_pre ) * sizeof(INT))) (j - 1 ) 0 c_pre (Znth (i - 1 ) rows __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i m_pre (i - 1 ) 0 r_pre c_pre rows )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i - 1 ) * c_pre ) + (j - 1 ) )) ”
.

Definition solver_safety_wit_20 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ ((j - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solver_safety_wit_21 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ (((i - 1 ) * c_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i - 1 ) * c_pre )) ”
.

Definition solver_safety_wit_22 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_23 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_25 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ (((c_pre + i ) * j ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((c_pre + i ) * j )) ”
.

Definition solver_safety_wit_26 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ ((c_pre + i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c_pre + i )) ”
.

Definition solver_safety_wit_27 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i > r_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= (r_pre + 1 ))) (PreH8 : (0 <= ((i - 1 ) * c_pre ))) (PreH9 : (((i - 1 ) * c_pre ) <= (r_pre * c_pre ))) (PreH10 : ((r_pre * c_pre ) <= 250000)) (PreH11 : (ConstructionPrefix r_pre c_pre rows ((i - 1 ) * c_pre ) )),
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows_2: (@list (@list (@option Z)))) __default__List__App_option_Z (PreH1 : (r_pre = 1)) (PreH2 : (ConstructionPrefix r_pre c_pre rows_2 0 )) (PreH3 : (c_pre <> 1)) (PreH4 : (r_pre = 1)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 500)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 500)),
  (IntArray2.mixed_full m_pre r_pre c_pre rows_2 )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (r_pre = 1) ”
  &&  “ (2 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows 0 ) ”
  &&  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
) \/
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows_2: (@list (@list (@option Z)))) __default__List__App_option_Z (PreH1 : (r_pre = 1)) (PreH2 : (ConstructionPrefix r_pre c_pre rows_2 0 )) (PreH3 : (c_pre <> 1)) (PreH4 : (r_pre = 1)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 500)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 500)),
  (IntArray2.mixed_full m_pre r_pre c_pre rows_2 )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (r_pre = 1) ”
  &&  “ (2 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows 0 ) ”
  &&  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
).

Definition solver_entail_wit_2 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows_2: (@list (@list (@option Z)))) __default__List__App_option_Z (PreH1 : (r_pre = 1)) (PreH2 : (2 <= c_pre)) (PreH3 : (c_pre <= 500)) (PreH4 : (ConstructionPrefix r_pre c_pre rows_2 0 )),
  (IntArray.mixed_full m_pre c_pre (Znth 0 rows_2 __default__List__App_option_Z) )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (r_pre = 1) ”
  &&  “ (2 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (c_pre + 1 )) ”
  &&  “ (0 <= (1 - 1 )) ”
  &&  “ ((1 - 1 ) <= c_pre) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows (1 - 1 ) ) ”
  &&  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
) \/
(
forall (r_pre: Z) (c_pre: Z) (rows_2: (@list (@list (@option Z)))) __default__List__App_option_Z (PreH1 : (r_pre = 1)) (PreH2 : (2 <= c_pre)) (PreH3 : (c_pre <= 500)) (PreH4 : (ConstructionPrefix r_pre c_pre rows_2 0 )),
  TT && emp 
|--
  EX (rows: (@list (@list (@option Z)))),
  “ ((Znth 0 rows_2 __default__List__App_option_Z) = (Znth 0 rows __default__List__App_option_Z)) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (c_pre + 1 )) ”
  &&  “ (0 <= (1 - 1 )) ”
  &&  “ ((1 - 1 ) <= c_pre) ”
  &&  “ (ConstructionPrefix 1 c_pre rows (1 - 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_3 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows_2: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows_2 (j - 1 ) )),
  (IntArray.mixed_full m_pre c_pre (replace_Znth ((j - 1 )) ((Some ((j + 1 )))) ((Znth 0 rows_2 __default__List__App_option_Z))) )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (r_pre = 1) ”
  &&  “ (2 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (1 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (c_pre + 1 )) ”
  &&  “ (0 <= ((j + 1 ) - 1 )) ”
  &&  “ (((j + 1 ) - 1 ) <= c_pre) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows ((j + 1 ) - 1 ) ) ”
  &&  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
) \/
(
forall (r_pre: Z) (c_pre: Z) (rows_2: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows_2 (j - 1 ) )),
  TT && emp 
|--
  EX (rows: (@list (@list (@option Z)))),
  “ ((replace_Znth ((j - 1 )) ((Some ((j + 1 )))) ((Znth 0 rows_2 __default__List__App_option_Z))) = (Znth 0 rows __default__List__App_option_Z)) ”
  &&  “ (1 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (c_pre + 1 )) ”
  &&  “ (0 <= ((j + 1 ) - 1 )) ”
  &&  “ (((j + 1 ) - 1 ) <= c_pre) ”
  &&  “ (ConstructionPrefix 1 c_pre rows ((j + 1 ) - 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_4 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows_2: (@list (@list (@option Z)))) (PreH1 : (r_pre <> 1)) (PreH2 : (ConstructionPrefix r_pre c_pre rows_2 0 )) (PreH3 : (r_pre <> 1)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 500)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 500)),
  (IntArray2.mixed_full m_pre r_pre c_pre rows_2 )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (2 <= r_pre) ”
  &&  “ (r_pre <= 500) ”
  &&  “ (1 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (r_pre + 1 )) ”
  &&  “ (0 <= ((1 - 1 ) * c_pre )) ”
  &&  “ (((1 - 1 ) * c_pre ) <= (r_pre * c_pre )) ”
  &&  “ ((r_pre * c_pre ) <= 250000) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows ((1 - 1 ) * c_pre ) ) ”
  &&  (IntArray2.mixed_full m_pre r_pre c_pre rows )
) \/
(
forall (r_pre: Z) (c_pre: Z) (rows_2: (@list (@list (@option Z)))) (PreH1 : (r_pre <> 1)) (PreH2 : (ConstructionPrefix r_pre c_pre rows_2 0 )) (PreH3 : (r_pre <> 1)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 500)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 500)),
  TT && emp 
|--
  “ (ConstructionPrefix r_pre c_pre rows_2 ((1 - 1 ) * c_pre ) ) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (r_pre: Z) (c_pre: Z) (rows_2: (@list (@list (@option Z)))) (PreH1 : (r_pre <> 1)) (PreH2 : (ConstructionPrefix r_pre c_pre rows_2 0 )) (PreH3 : (r_pre <> 1)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 500)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 500)),
  (ConstructionPrefix r_pre c_pre rows_2 ((1 - 1 ) * c_pre ) )
.

Definition solver_entail_wit_5 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows_2: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i <= r_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= (r_pre + 1 ))) (PreH8 : (0 <= ((i - 1 ) * c_pre ))) (PreH9 : (((i - 1 ) * c_pre ) <= (r_pre * c_pre ))) (PreH10 : ((r_pre * c_pre ) <= 250000)) (PreH11 : (ConstructionPrefix r_pre c_pre rows_2 ((i - 1 ) * c_pre ) )),
  (IntArray2.mixed_full m_pre r_pre c_pre rows_2 )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (2 <= r_pre) ”
  &&  “ (r_pre <= 500) ”
  &&  “ (1 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (c_pre + 1 )) ”
  &&  “ (0 <= (((i - 1 ) * c_pre ) + (1 - 1 ) )) ”
  &&  “ ((((i - 1 ) * c_pre ) + (1 - 1 ) ) <= (r_pre * c_pre )) ”
  &&  “ ((r_pre * c_pre ) <= 250000) ”
  &&  “ (1 <= ((c_pre + i ) * 1 )) ”
  &&  “ ((1 <= c_pre) -> (((c_pre + i ) * 1 ) <= 500000)) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (1 - 1 ) ) ) ”
  &&  (IntArray2.mixed_full m_pre r_pre c_pre rows )
) \/
(
forall (r_pre: Z) (c_pre: Z) (rows_2: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i <= r_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= (r_pre + 1 ))) (PreH8 : (0 <= ((i - 1 ) * c_pre ))) (PreH9 : (((i - 1 ) * c_pre ) <= (r_pre * c_pre ))) (PreH10 : ((r_pre * c_pre ) <= 250000)) (PreH11 : (ConstructionPrefix r_pre c_pre rows_2 ((i - 1 ) * c_pre ) )),
  TT && emp 
|--
  “ (ConstructionPrefix r_pre c_pre rows_2 (((i - 1 ) * c_pre ) + (1 - 1 ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (r_pre: Z) (c_pre: Z) (rows_2: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i <= r_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= (r_pre + 1 ))) (PreH8 : (0 <= ((i - 1 ) * c_pre ))) (PreH9 : (((i - 1 ) * c_pre ) <= (r_pre * c_pre ))) (PreH10 : ((r_pre * c_pre ) <= 250000)) (PreH11 : (ConstructionPrefix r_pre c_pre rows_2 ((i - 1 ) * c_pre ) )),
  (ConstructionPrefix r_pre c_pre rows_2 (((i - 1 ) * c_pre ) + (1 - 1 ) ) )
.

Definition solver_entail_wit_6 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j > c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows_2 (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  (IntArray2.mixed_full m_pre r_pre c_pre rows_2 )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (2 <= r_pre) ”
  &&  “ (r_pre <= 500) ”
  &&  “ (1 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (r_pre + 1 )) ”
  &&  “ (0 <= (((i + 1 ) - 1 ) * c_pre )) ”
  &&  “ ((((i + 1 ) - 1 ) * c_pre ) <= (r_pre * c_pre )) ”
  &&  “ ((r_pre * c_pre ) <= 250000) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows (((i + 1 ) - 1 ) * c_pre ) ) ”
  &&  (IntArray2.mixed_full m_pre r_pre c_pre rows )
) \/
(
forall (r_pre: Z) (c_pre: Z) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j > c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows_2 (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  TT && emp 
|--
  “ (ConstructionPrefix r_pre c_pre rows_2 (((i + 1 ) - 1 ) * c_pre ) ) ”
  &&  “ ((((i + 1 ) - 1 ) * c_pre ) <= (r_pre * c_pre )) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (r_pre: Z) (c_pre: Z) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j > c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows_2 (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  (ConstructionPrefix r_pre c_pre rows_2 (((i + 1 ) - 1 ) * c_pre ) )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (r_pre: Z) (c_pre: Z) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j > c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows_2 (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  ((((i + 1 ) - 1 ) * c_pre ) <= (r_pre * c_pre ))
.

Definition solver_entail_wit_7 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows_2 (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  (((m_pre + ((((i - 1 ) * c_pre ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> ((c_pre + i ) * j ))
  **  (IntArray.mixed_missing_i (m_pre + (((i - 1 ) * c_pre ) * sizeof(INT))) (j - 1 ) 0 c_pre (Znth (i - 1 ) rows_2 __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i m_pre (i - 1 ) 0 r_pre c_pre rows_2 )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (2 <= r_pre) ”
  &&  “ (r_pre <= 500) ”
  &&  “ (1 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (1 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (c_pre + 1 )) ”
  &&  “ (0 <= (((i - 1 ) * c_pre ) + ((j + 1 ) - 1 ) )) ”
  &&  “ ((((i - 1 ) * c_pre ) + ((j + 1 ) - 1 ) ) <= (r_pre * c_pre )) ”
  &&  “ ((r_pre * c_pre ) <= 250000) ”
  &&  “ (1 <= ((c_pre + i ) * (j + 1 ) )) ”
  &&  “ (((j + 1 ) <= c_pre) -> (((c_pre + i ) * (j + 1 ) ) <= 500000)) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + ((j + 1 ) - 1 ) ) ) ”
  &&  (IntArray2.mixed_full m_pre r_pre c_pre rows )
) \/
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z) __default__List__App_option_Z (PreH1 : (((c_pre + i ) * j ) <= INT_MAX)) (PreH2 : (((c_pre + i ) * j ) >= INT_MIN)) (PreH3 : (j <= c_pre)) (PreH4 : (2 <= r_pre)) (PreH5 : (r_pre <= 500)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 500)) (PreH8 : (1 <= i)) (PreH9 : (i <= r_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= (c_pre + 1 ))) (PreH12 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH13 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH14 : ((r_pre * c_pre ) <= 250000)) (PreH15 : (1 <= ((c_pre + i ) * j ))) (PreH16 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH17 : (ConstructionPrefix r_pre c_pre rows_2 (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  (((m_pre + ((((i - 1 ) * c_pre ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> ((c_pre + i ) * j ))
  **  (IntArray.mixed_missing_i (m_pre + (((i - 1 ) * c_pre ) * sizeof(INT))) (j - 1 ) 0 c_pre (Znth (i - 1 ) rows_2 __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i m_pre (i - 1 ) 0 r_pre c_pre rows_2 )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (2 <= r_pre) ”
  &&  “ (r_pre <= 500) ”
  &&  “ (1 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (1 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (c_pre + 1 )) ”
  &&  “ (0 <= (((i - 1 ) * c_pre ) + ((j + 1 ) - 1 ) )) ”
  &&  “ ((((i - 1 ) * c_pre ) + ((j + 1 ) - 1 ) ) <= (r_pre * c_pre )) ”
  &&  “ ((r_pre * c_pre ) <= 250000) ”
  &&  “ (1 <= ((c_pre + i ) * (j + 1 ) )) ”
  &&  “ (((j + 1 ) <= c_pre) -> (((c_pre + i ) * (j + 1 ) ) <= 500000)) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + ((j + 1 ) - 1 ) ) ) ”
  &&  (IntArray2.mixed_full m_pre r_pre c_pre rows )
).

Definition solver_return_wit_1 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i > r_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= (r_pre + 1 ))) (PreH8 : (0 <= ((i - 1 ) * c_pre ))) (PreH9 : (((i - 1 ) * c_pre ) <= (r_pre * c_pre ))) (PreH10 : ((r_pre * c_pre ) <= 250000)) (PreH11 : (ConstructionPrefix r_pre c_pre rows ((i - 1 ) * c_pre ) )),
  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  EX (matrix: (@list (@list Z))) (out_spec: (@option (@list (@list Z)))),
  “ (Spec r_pre c_pre out_spec ) ”
  &&  “ (out_spec = (Some (matrix))) ”
  &&  “ (1 = 1) ”
  &&  (IntArray2.full m_pre r_pre c_pre matrix )
) \/
(
forall (r_pre: Z) (c_pre: Z) (rows: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i > r_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= (r_pre + 1 ))) (PreH8 : (0 <= ((i - 1 ) * c_pre ))) (PreH9 : (((i - 1 ) * c_pre ) <= (r_pre * c_pre ))) (PreH10 : ((r_pre * c_pre ) <= 250000)) (PreH11 : (ConstructionPrefix r_pre c_pre rows ((i - 1 ) * c_pre ) )),
  TT && emp 
|--
  EX (matrix: (@list (@list Z))),
  “ (rows = (Array2.some_rows (matrix))) ”
  &&  “ (Spec r_pre c_pre (Some (matrix)) ) ”
  &&  emp
).

Definition solver_return_wit_2 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j > c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows (j - 1 ) )),
  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
|--
  EX (matrix: (@list (@list Z))) (out_spec: (@option (@list (@list Z)))),
  “ (Spec r_pre c_pre out_spec ) ”
  &&  “ (out_spec = (Some (matrix))) ”
  &&  “ (1 = 1) ”
  &&  (IntArray2.full m_pre r_pre c_pre matrix )
) \/
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j > c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows (j - 1 ) )),
  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
|--
  EX (matrix: (@list (@list Z))),
  “ (Spec r_pre c_pre (Some (matrix)) ) ”
  &&  (IntArray2.full m_pre r_pre c_pre matrix )
).

Definition solver_return_wit_3 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (PreH1 : (c_pre = 1)) (PreH2 : (r_pre = 1)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 500)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 500)),
  (IntArray2.undef_full m_pre r_pre c_pre )
|--
  EX (out_spec: (@option (@list (@list Z)))),
  “ (Spec r_pre c_pre out_spec ) ”
  &&  “ (out_spec = None) ”
  &&  “ (0 = 0) ”
  &&  (IntArray2.undef_full m_pre r_pre c_pre )
) \/
(
forall (r_pre: Z) (c_pre: Z) (PreH1 : (c_pre = 1)) (PreH2 : (r_pre = 1)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 500)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 500)),
  TT && emp 
|--
  “ (Spec 1 1 None ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 :=
forall (r_pre: Z) (c_pre: Z) (PreH1 : (c_pre = 1)) (PreH2 : (r_pre = 1)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 500)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 500)),
  (Spec 1 1 None )
.

Definition solver_partial_solve_wit_1 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (PreH1 : (c_pre <> 1)) (PreH2 : (r_pre = 1)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 500)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 500)),
  (IntArray2.undef_full m_pre r_pre c_pre )
|--
  “ (c_pre <> 1) ”
  &&  “ (r_pre = 1) ”
  &&  “ (1 <= r_pre) ”
  &&  “ (r_pre <= 500) ”
  &&  “ (1 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  (IntArray2.undef_full m_pre r_pre c_pre )
.

Definition solver_partial_solve_wit_2 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (PreH1 : (r_pre <> 1)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)),
  (IntArray2.undef_full m_pre r_pre c_pre )
|--
  “ (r_pre <> 1) ”
  &&  “ (1 <= r_pre) ”
  &&  “ (r_pre <= 500) ”
  &&  “ (1 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  (IntArray2.undef_full m_pre r_pre c_pre )
.

Definition solver_partial_solve_wit_3 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (r_pre = 1)) (PreH3 : (2 <= c_pre)) (PreH4 : (c_pre <= 500)) (PreH5 : (1 <= j)) (PreH6 : (j <= (c_pre + 1 ))) (PreH7 : (0 <= (j - 1 ))) (PreH8 : ((j - 1 ) <= c_pre)) (PreH9 : (ConstructionPrefix r_pre c_pre rows (j - 1 ) )),
  (IntArray.mixed_full m_pre c_pre (Znth 0 rows __default__List__App_option_Z) )
|--
  “ (j <= c_pre) ”
  &&  “ (r_pre = 1) ”
  &&  “ (2 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (1 <= j) ”
  &&  “ (j <= (c_pre + 1 )) ”
  &&  “ (0 <= (j - 1 )) ”
  &&  “ ((j - 1 ) <= c_pre) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows (j - 1 ) ) ”
  &&  (((m_pre + ((j - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i m_pre (j - 1 ) 0 c_pre (Znth 0 rows __default__List__App_option_Z) )
.

Definition solver_partial_solve_wit_4 :=
forall (r_pre: Z) (c_pre: Z) (m_pre: Z) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) __default__List__App_option_Z (PreH1 : (j <= c_pre)) (PreH2 : (2 <= r_pre)) (PreH3 : (r_pre <= 500)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 500)) (PreH6 : (1 <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (c_pre + 1 ))) (PreH10 : (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre ))) (PreH12 : ((r_pre * c_pre ) <= 250000)) (PreH13 : (1 <= ((c_pre + i ) * j ))) (PreH14 : ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000))) (PreH15 : (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) )),
  (IntArray2.mixed_full m_pre r_pre c_pre rows )
|--
  “ (j <= c_pre) ”
  &&  “ (2 <= r_pre) ”
  &&  “ (r_pre <= 500) ”
  &&  “ (1 <= c_pre) ”
  &&  “ (c_pre <= 500) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (1 <= j) ”
  &&  “ (j <= (c_pre + 1 )) ”
  &&  “ (0 <= (((i - 1 ) * c_pre ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * c_pre ) + (j - 1 ) ) <= (r_pre * c_pre )) ”
  &&  “ ((r_pre * c_pre ) <= 250000) ”
  &&  “ (1 <= ((c_pre + i ) * j )) ”
  &&  “ ((j <= c_pre) -> (((c_pre + i ) * j ) <= 500000)) ”
  &&  “ (ConstructionPrefix r_pre c_pre rows (((i - 1 ) * c_pre ) + (j - 1 ) ) ) ”
  &&  (((m_pre + ((((i - 1 ) * c_pre ) + (j - 1 ) ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i (m_pre + (((i - 1 ) * c_pre ) * sizeof(INT))) (j - 1 ) 0 c_pre (Znth (i - 1 ) rows __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i m_pre (i - 1 ) 0 r_pre c_pre rows )
.

Definition solver_which_implies_wit_1 :=
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z),
  (IntArray2.undef_full m_pre r_pre c_pre )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (ConstructionPrefix r_pre c_pre rows 0 ) ”
  &&  (IntArray2.mixed_full m_pre r_pre c_pre rows )
) \/
(
forall (r_pre: Z) (c_pre: Z) (m_pre: Z),
  (IntArray2.undef_full m_pre r_pre c_pre )
|--
  EX (rows: (@list (@list (@option Z)))),
  “ (ConstructionPrefix r_pre c_pre rows 0 ) ”
  &&  (IntArray2.mixed_full m_pre r_pre c_pre rows )
).

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include array2_ext_Strategy_Correct.

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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.

End VC_Correct.
