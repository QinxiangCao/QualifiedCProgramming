From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int64  |-> i_pre)
  **  ((( &( "j" ) )) # Int64  |-> j_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 4 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int64  |-> i_pre)
  **  ((( &( "j" ) )) # Int64  |-> j_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.undef_full out_pre 4 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 :=
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
  **  (Int64Array.undef_seg out_pre 1 4 )
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int64  |-> i_pre)
  **  ((( &( "j" ) )) # Int64  |-> j_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 :=
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
  **  (Int64Array.undef_seg out_pre 1 4 )
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int64  |-> i_pre)
  **  ((( &( "j" ) )) # Int64  |-> j_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  (((out_pre + (1 * sizeof(INT64)))) # Int64  |-> 1)
  **  (Int64Array.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int64  |-> i_pre)
  **  ((( &( "j" ) )) # Int64  |-> j_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_6 :=
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  (Int64Array.undef_seg out_pre ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT64)))) # Int64  |-> n_pre)
  **  (((out_pre + (1 * sizeof(INT64)))) # Int64  |-> 1)
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int64  |-> i_pre)
  **  ((( &( "j" ) )) # Int64  |-> j_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_return_wit_1 :=
(
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  (Int64Array.undef_seg out_pre (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((out_pre + (3 * sizeof(INT64)))) # Int64  |-> m_pre)
  **  (((out_pre + (2 * sizeof(INT64)))) # Int64  |-> n_pre)
  **  (((out_pre + (1 * sizeof(INT64)))) # Int64  |-> 1)
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
|--
  EX (p: (Z * Z)) (q: (Z * Z)),
  “ (Spec n_pre m_pre start p q ) ”
  &&  (Int64Array.full out_pre 4 (cons ((zpair_fst (p))) ((cons ((zpair_snd (p))) ((cons ((zpair_fst (q))) ((cons ((zpair_snd (q))) ((@nil Z))))))))) )
) \/
(
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= INT64_MAX)) (PreH2 : (n_pre <= INT64_MAX)) (PreH3 : (m_pre <= INT64_MAX)) (PreH4 : (1 >= INT64_MIN)) (PreH5 : (n_pre >= INT64_MIN)) (PreH6 : (m_pre >= INT64_MIN)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 1000000000)) (PreH11 : (i_pre = (zpair_fst (start)))) (PreH12 : (j_pre = (zpair_snd (start)))) (PreH13 : (1 <= i_pre)) (PreH14 : (i_pre <= n_pre)) (PreH15 : (1 <= j_pre)) (PreH16 : (j_pre <= m_pre)),
  (((out_pre + (3 * sizeof(INT64)))) # Int64  |-> m_pre)
  **  (((out_pre + (2 * sizeof(INT64)))) # Int64  |-> n_pre)
  **  (((out_pre + (1 * sizeof(INT64)))) # Int64  |-> 1)
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
|--
  EX (p: (Z * Z)) (q: (Z * Z)),
  “ (Spec n_pre m_pre start p q ) ”
  &&  (Int64Array.full out_pre 4 (cons ((zpair_fst (p))) ((cons ((zpair_snd (p))) ((cons ((zpair_fst (q))) ((cons ((zpair_snd (q))) ((@nil Z))))))))) )
).

Definition solver_partial_solve_wit_1 :=
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  (Int64Array.undef_full out_pre 4 )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000000) ”
  &&  “ (i_pre = (zpair_fst (start))) ”
  &&  “ (j_pre = (zpair_snd (start))) ”
  &&  “ (1 <= i_pre) ”
  &&  “ (i_pre <= n_pre) ”
  &&  “ (1 <= j_pre) ”
  &&  “ (j_pre <= m_pre) ”
  &&  (((out_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg out_pre 1 4 )
.

Definition solver_partial_solve_wit_2 :=
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
  **  (Int64Array.undef_seg out_pre 1 4 )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000000) ”
  &&  “ (i_pre = (zpair_fst (start))) ”
  &&  “ (j_pre = (zpair_snd (start))) ”
  &&  “ (1 <= i_pre) ”
  &&  “ (i_pre <= n_pre) ”
  &&  “ (1 <= j_pre) ”
  &&  “ (j_pre <= m_pre) ”
  &&  (((out_pre + (1 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
.

Definition solver_partial_solve_wit_3 :=
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  (((out_pre + (1 * sizeof(INT64)))) # Int64  |-> 1)
  **  (Int64Array.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000000) ”
  &&  “ (i_pre = (zpair_fst (start))) ”
  &&  “ (j_pre = (zpair_snd (start))) ”
  &&  “ (1 <= i_pre) ”
  &&  “ (i_pre <= n_pre) ”
  &&  “ (1 <= j_pre) ”
  &&  “ (j_pre <= m_pre) ”
  &&  (((out_pre + (2 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i out_pre 2 (1 + 1 ) 4 )
  **  (((out_pre + (1 * sizeof(INT64)))) # Int64  |-> 1)
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
.

Definition solver_partial_solve_wit_4 :=
forall (start: (Z * Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (out_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)),
  (Int64Array.undef_seg out_pre ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT64)))) # Int64  |-> n_pre)
  **  (((out_pre + (1 * sizeof(INT64)))) # Int64  |-> 1)
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000000) ”
  &&  “ (i_pre = (zpair_fst (start))) ”
  &&  “ (j_pre = (zpair_snd (start))) ”
  &&  “ (1 <= i_pre) ”
  &&  “ (i_pre <= n_pre) ”
  &&  “ (1 <= j_pre) ”
  &&  “ (j_pre <= m_pre) ”
  &&  (((out_pre + (3 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i out_pre 3 ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT64)))) # Int64  |-> n_pre)
  **  (((out_pre + (1 * sizeof(INT64)))) # Int64  |-> 1)
  **  (((out_pre + (0 * sizeof(INT64)))) # Int64  |-> 1)
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.

End VC_Correct.
