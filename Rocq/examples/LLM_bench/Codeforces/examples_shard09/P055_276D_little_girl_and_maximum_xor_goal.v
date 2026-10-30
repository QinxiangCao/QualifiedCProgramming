From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (l_pre: Z) (r_pre: Z) (PreH1 : (1 <= l_pre)) (PreH2 : (l_pre <= r_pre)) (PreH3 : (r_pre <= 1000000000000000000)),
  ((( &( "x" ) )) # UInt64  |-> (Z.lxor l_pre r_pre))
  **  ((( &( "l" ) )) # UInt64  |-> l_pre)
  **  ((( &( "r" ) )) # UInt64  |-> r_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (l_pre: Z) (r_pre: Z) (PreH1 : ((Z.lxor l_pre r_pre) = 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)),
  ((( &( "x" ) )) # UInt64  |-> (Z.lxor l_pre r_pre))
  **  ((( &( "l" ) )) # UInt64  |-> l_pre)
  **  ((( &( "r" ) )) # UInt64  |-> r_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (l_pre: Z) (r_pre: Z) (PreH1 : ((Z.lxor l_pre r_pre) <> 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # UInt64  |-> (Z.lxor l_pre r_pre))
  **  ((( &( "l" ) )) # UInt64  |-> l_pre)
  **  ((( &( "r" ) )) # UInt64  |-> r_pre)
|--
  “ (63 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 63) ”
.

Definition solver_safety_wit_4 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (1 <= l_pre)) (PreH2 : (l_pre <= r_pre)) (PreH3 : (r_pre <= 1000000000000000000)) (PreH4 : (0 < x)) (PreH5 : (x <= UINT64_MAX)) (PreH6 : (0 <= b)) (PreH7 : (b <= 63)) (PreH8 : (HighestBitScan l_pre r_pre x b )),
  ((( &( "l" ) )) # UInt64  |-> l_pre)
  **  ((( &( "r" ) )) # UInt64  |-> r_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x)
  **  ((( &( "b" ) )) # Int  |-> b)
|--
  “ (b <= 63) ”
  &&  “ (0 <= b) ”
.

Definition solver_safety_wit_5 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : ((Z.land (Z.shiftr x b) 1) = 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : (0 < x)) (PreH6 : (x <= UINT64_MAX)) (PreH7 : (0 <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b )),
  ((( &( "l" ) )) # UInt64  |-> l_pre)
  **  ((( &( "r" ) )) # UInt64  |-> r_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x)
  **  ((( &( "b" ) )) # Int  |-> b)
|--
  “ ((b - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (b - 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : (0 < x)) (PreH6 : (x <= UINT64_MAX)) (PreH7 : (0 <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b )),
  ((( &( "l" ) )) # UInt64  |-> l_pre)
  **  ((( &( "r" ) )) # UInt64  |-> r_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x)
  **  ((( &( "b" ) )) # Int  |-> b)
|--
  “ (63 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 63) ”
.

Definition solver_safety_wit_7 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (b <> 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : (0 < x)) (PreH7 : (x <= UINT64_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b )),
  ((( &( "l" ) )) # UInt64  |-> l_pre)
  **  ((( &( "r" ) )) # UInt64  |-> r_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x)
  **  ((( &( "b" ) )) # Int  |-> b)
|--
  “ ((b + 1 ) <= 63) ”
  &&  “ (0 <= (b + 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (b <> 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : (0 < x)) (PreH7 : (x <= UINT64_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b )),
  ((( &( "l" ) )) # UInt64  |-> l_pre)
  **  ((( &( "r" ) )) # UInt64  |-> r_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x)
  **  ((( &( "b" ) )) # Int  |-> b)
|--
  “ ((b + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (b + 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (b <> 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : (0 < x)) (PreH7 : (x <= UINT64_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b )),
  ((( &( "l" ) )) # UInt64  |-> l_pre)
  **  ((( &( "r" ) )) # UInt64  |-> r_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x)
  **  ((( &( "b" ) )) # Int  |-> b)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (b <> 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : (0 < x)) (PreH7 : (x <= UINT64_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b )),
  ((( &( "l" ) )) # UInt64  |-> l_pre)
  **  ((( &( "r" ) )) # UInt64  |-> r_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x)
  **  ((( &( "b" ) )) # Int  |-> b)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (l_pre: Z) (r_pre: Z) (PreH1 : ((Z.lxor l_pre r_pre) <> 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (1 <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= 1000000000000000000) ”
  &&  “ (0 < (Z.lxor l_pre r_pre)) ”
  &&  “ ((Z.lxor l_pre r_pre) <= UINT64_MAX) ”
  &&  “ (0 <= 63) ”
  &&  “ (63 <= 63) ”
  &&  “ (HighestBitScan l_pre r_pre (Z.lxor l_pre r_pre) 63 ) ”
  &&  emp
) \/
(
forall (l_pre: Z) (r_pre: Z) (PreH1 : ((Z.lxor l_pre r_pre) <> 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (HighestBitScan l_pre r_pre (Z.lxor l_pre r_pre) 63 ) ”
  &&  “ ((Z.lxor l_pre r_pre) <= UINT64_MAX) ”
  &&  “ (0 < (Z.lxor l_pre r_pre)) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (l_pre: Z) (r_pre: Z) (PreH1 : ((Z.lxor l_pre r_pre) <> 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)),
  (HighestBitScan l_pre r_pre (Z.lxor l_pre r_pre) 63 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (l_pre: Z) (r_pre: Z) (PreH1 : ((Z.lxor l_pre r_pre) <> 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)),
  ((Z.lxor l_pre r_pre) <= UINT64_MAX)
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (l_pre: Z) (r_pre: Z) (PreH1 : ((Z.lxor l_pre r_pre) <> 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)),
  (0 < (Z.lxor l_pre r_pre))
.

Definition solver_entail_wit_2 :=
(
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : ((Z.land (Z.shiftr x b) 1) = 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : (0 < x)) (PreH6 : (x <= UINT64_MAX)) (PreH7 : (0 <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b )),
  TT && emp 
|--
  “ (1 <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= 1000000000000000000) ”
  &&  “ (0 < x) ”
  &&  “ (x <= UINT64_MAX) ”
  &&  “ (0 <= (b - 1 )) ”
  &&  “ ((b - 1 ) <= 63) ”
  &&  “ (HighestBitScan l_pre r_pre x (b - 1 ) ) ”
  &&  emp
) \/
(
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : ((Z.land (Z.shiftr x b) 1) = 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : (0 < x)) (PreH6 : (x <= UINT64_MAX)) (PreH7 : (0 <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b )),
  TT && emp 
|--
  “ (HighestBitScan l_pre r_pre x (b - 1 ) ) ”
  &&  “ (0 <= (b - 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : ((Z.land (Z.shiftr x b) 1) = 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : (0 < x)) (PreH6 : (x <= UINT64_MAX)) (PreH7 : (0 <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b )),
  (HighestBitScan l_pre r_pre x (b - 1 ) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : ((Z.land (Z.shiftr x b) 1) = 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : (0 < x)) (PreH6 : (x <= UINT64_MAX)) (PreH7 : (0 <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b )),
  (0 <= (b - 1 ))
.

Definition solver_return_wit_1 :=
(
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (b = 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : (0 < x)) (PreH7 : (x <= UINT64_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b )),
  TT && emp 
|--
  “ (Spec l_pre r_pre (unsigned_last_nbits ((Z.lnot 0)) (64)) ) ”
  &&  emp
) \/
(
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (b = 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : (0 < x)) (PreH7 : (x <= UINT64_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b )),
  TT && emp 
|--
  “ (Spec l_pre r_pre (unsigned_last_nbits ((Z.lnot 0)) (64)) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (b = 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : (0 < x)) (PreH7 : (x <= UINT64_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b )),
  (Spec l_pre r_pre (unsigned_last_nbits ((Z.lnot 0)) (64)) )
.

Definition solver_return_wit_2 :=
(
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (b <> 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : (0 < x)) (PreH7 : (x <= UINT64_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b )),
  TT && emp 
|--
  “ (Spec l_pre r_pre (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl 1 (b + 1 ))) (64)) - 1 )) (64)) ) ”
  &&  emp
) \/
(
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (b <> 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : (0 < x)) (PreH7 : (x <= UINT64_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b )),
  TT && emp 
|--
  “ (Spec l_pre r_pre (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl 1 (b + 1 ))) (64)) - 1 )) (64)) ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (l_pre: Z) (r_pre: Z) (b: Z) (x: Z) (PreH1 : (b <> 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) <> 0)) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : (0 < x)) (PreH7 : (x <= UINT64_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b )),
  (Spec l_pre r_pre (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl 1 (b + 1 ))) (64)) - 1 )) (64)) )
.

Definition solver_return_wit_3 :=
(
forall (l_pre: Z) (r_pre: Z) (PreH1 : ((Z.lxor l_pre r_pre) = 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (Spec l_pre r_pre 0 ) ”
  &&  emp
) \/
(
forall (l_pre: Z) (r_pre: Z) (PreH1 : ((Z.lxor l_pre r_pre) = 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)),
  TT && emp 
|--
  “ (Spec l_pre r_pre 0 ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 :=
forall (l_pre: Z) (r_pre: Z) (PreH1 : ((Z.lxor l_pre r_pre) = 0)) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)),
  (Spec l_pre r_pre 0 )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.

End VC_Correct.
