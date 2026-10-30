From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P045_569A_music_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (PreH1 : (2 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : (1 <= s_pre)) (PreH4 : (s_pre < t_pre)) (PreH5 : (t_pre <= 100000)),
  ((( &( "starts" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "s" ) )) # Int64  |-> s_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (starts: Z) (s: Z) (PreH1 : (s < t_pre)) (PreH2 : (2 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : (1 <= s_pre)) (PreH5 : (s_pre < t_pre)) (PreH6 : (t_pre <= 100000)) (PreH7 : (1 <= s)) (PreH8 : (s <= ((t_pre - 1 ) * q_pre ))) (PreH9 : (0 <= starts)) (PreH10 : (starts < s)) (PreH11 : (MusicLoopInvariant t_pre s_pre q_pre starts s )),
  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "starts" ) )) # Int  |-> starts)
|--
  “ ((s * q_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s * q_pre )) ”
.

Definition solver_safety_wit_3 :=
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (starts: Z) (s: Z) (PreH1 : (s < t_pre)) (PreH2 : (2 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : (1 <= s_pre)) (PreH5 : (s_pre < t_pre)) (PreH6 : (t_pre <= 100000)) (PreH7 : (1 <= s)) (PreH8 : (s <= ((t_pre - 1 ) * q_pre ))) (PreH9 : (0 <= starts)) (PreH10 : (starts < s)) (PreH11 : (MusicLoopInvariant t_pre s_pre q_pre starts s )),
  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "s" ) )) # Int64  |-> (s * q_pre ))
  **  ((( &( "starts" ) )) # Int  |-> starts)
|--
  “ ((starts + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (starts + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (PreH1 : (2 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : (1 <= s_pre)) (PreH4 : (s_pre < t_pre)) (PreH5 : (t_pre <= 100000)),
  TT && emp 
|--
  “ (2 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre < t_pre) ”
  &&  “ (t_pre <= 100000) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= ((t_pre - 1 ) * q_pre )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < s_pre) ”
  &&  “ (MusicLoopInvariant t_pre s_pre q_pre 0 s_pre ) ”
  &&  emp
) \/
(
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (PreH1 : (2 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : (1 <= s_pre)) (PreH4 : (s_pre < t_pre)) (PreH5 : (t_pre <= 100000)),
  TT && emp 
|--
  “ (MusicLoopInvariant t_pre s_pre q_pre 0 s_pre ) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (PreH1 : (2 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : (1 <= s_pre)) (PreH4 : (s_pre < t_pre)) (PreH5 : (t_pre <= 100000)),
  (MusicLoopInvariant t_pre s_pre q_pre 0 s_pre )
.

Definition solver_entail_wit_2 :=
(
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (starts: Z) (s: Z) (PreH1 : (s < t_pre)) (PreH2 : (2 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : (1 <= s_pre)) (PreH5 : (s_pre < t_pre)) (PreH6 : (t_pre <= 100000)) (PreH7 : (1 <= s)) (PreH8 : (s <= ((t_pre - 1 ) * q_pre ))) (PreH9 : (0 <= starts)) (PreH10 : (starts < s)) (PreH11 : (MusicLoopInvariant t_pre s_pre q_pre starts s )),
  TT && emp 
|--
  “ (2 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre < t_pre) ”
  &&  “ (t_pre <= 100000) ”
  &&  “ (1 <= (s * q_pre )) ”
  &&  “ ((s * q_pre ) <= ((t_pre - 1 ) * q_pre )) ”
  &&  “ (0 <= (starts + 1 )) ”
  &&  “ ((starts + 1 ) < (s * q_pre )) ”
  &&  “ (MusicLoopInvariant t_pre s_pre q_pre (starts + 1 ) (s * q_pre ) ) ”
  &&  emp
) \/
(
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (starts: Z) (s: Z) (PreH1 : (s < t_pre)) (PreH2 : (2 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : (1 <= s_pre)) (PreH5 : (s_pre < t_pre)) (PreH6 : (t_pre <= 100000)) (PreH7 : (1 <= s)) (PreH8 : (s <= ((t_pre - 1 ) * q_pre ))) (PreH9 : (0 <= starts)) (PreH10 : (starts < s)) (PreH11 : (MusicLoopInvariant t_pre s_pre q_pre starts s )),
  TT && emp 
|--
  “ (MusicLoopInvariant t_pre s_pre q_pre (starts + 1 ) (s * q_pre ) ) ”
  &&  “ ((s * q_pre ) <= ((t_pre - 1 ) * q_pre )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (starts: Z) (s: Z) (PreH1 : (s < t_pre)) (PreH2 : (2 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : (1 <= s_pre)) (PreH5 : (s_pre < t_pre)) (PreH6 : (t_pre <= 100000)) (PreH7 : (1 <= s)) (PreH8 : (s <= ((t_pre - 1 ) * q_pre ))) (PreH9 : (0 <= starts)) (PreH10 : (starts < s)) (PreH11 : (MusicLoopInvariant t_pre s_pre q_pre starts s )),
  (MusicLoopInvariant t_pre s_pre q_pre (starts + 1 ) (s * q_pre ) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (starts: Z) (s: Z) (PreH1 : (s < t_pre)) (PreH2 : (2 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : (1 <= s_pre)) (PreH5 : (s_pre < t_pre)) (PreH6 : (t_pre <= 100000)) (PreH7 : (1 <= s)) (PreH8 : (s <= ((t_pre - 1 ) * q_pre ))) (PreH9 : (0 <= starts)) (PreH10 : (starts < s)) (PreH11 : (MusicLoopInvariant t_pre s_pre q_pre starts s )),
  ((s * q_pre ) <= ((t_pre - 1 ) * q_pre ))
.

Definition solver_return_wit_1 :=
(
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (starts: Z) (s: Z) (PreH1 : (s >= t_pre)) (PreH2 : (2 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : (1 <= s_pre)) (PreH5 : (s_pre < t_pre)) (PreH6 : (t_pre <= 100000)) (PreH7 : (1 <= s)) (PreH8 : (s <= ((t_pre - 1 ) * q_pre ))) (PreH9 : (0 <= starts)) (PreH10 : (starts < s)) (PreH11 : (MusicLoopInvariant t_pre s_pre q_pre starts s )),
  TT && emp 
|--
  “ (Spec t_pre s_pre q_pre starts ) ”
  &&  emp
) \/
(
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (starts: Z) (s: Z) (PreH1 : (s >= t_pre)) (PreH2 : (2 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : (1 <= s_pre)) (PreH5 : (s_pre < t_pre)) (PreH6 : (t_pre <= 100000)) (PreH7 : (1 <= s)) (PreH8 : (s <= ((t_pre - 1 ) * q_pre ))) (PreH9 : (0 <= starts)) (PreH10 : (starts < s)) (PreH11 : (MusicLoopInvariant t_pre s_pre q_pre starts s )),
  TT && emp 
|--
  “ (Spec t_pre s_pre q_pre starts ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (t_pre: Z) (s_pre: Z) (q_pre: Z) (starts: Z) (s: Z) (PreH1 : (s >= t_pre)) (PreH2 : (2 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : (1 <= s_pre)) (PreH5 : (s_pre < t_pre)) (PreH6 : (t_pre <= 100000)) (PreH7 : (1 <= s)) (PreH8 : (s <= ((t_pre - 1 ) * q_pre ))) (PreH9 : (0 <= starts)) (PreH10 : (starts < s)) (PreH11 : (MusicLoopInvariant t_pre s_pre q_pre starts s )),
  (Spec t_pre s_pre q_pre starts )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.

End VC_Correct.
