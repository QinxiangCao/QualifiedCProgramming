From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (text: (@list Z)) (s_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))),
  ((( &( "next" ) )) # Char  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_2 :=
forall (text: (@list Z)) (s_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next" ) )) # Char  |-> 97)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) > next)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 500)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (97 <= next)) (PreH8 : (next <= 122)) (PreH9 : (ObfuscationPrefixState text i next )) (PreH10 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "next" ) )) # Char  |-> next)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next )) (PreH11 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "next" ) )) # Char  |-> next)
|--
  “ (122 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 122) ”
.

Definition solver_safety_wit_5 :=
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : (next < 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "next" ) )) # Char  |-> next)
|--
  “ ((next + 1 ) <= 127) ”
  &&  “ ((-128) <= (next + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : (next < 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "next" ) )) # Char  |-> (next + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> next)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next )) (PreH11 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "next" ) )) # Char  |-> next)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : (next >= 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "next" ) )) # Char  |-> next)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next )) (PreH9 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "next" ) )) # Char  |-> next)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (text: (@list Z)) (s_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 500) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (text))) ”
  &&  “ (97 <= 97) ”
  &&  “ (97 <= 122) ”
  &&  “ (ObfuscationPrefixState text 0 97 ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))),
  TT && emp 
|--
  “ (ObfuscationPrefixState text 0 97 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))),
  (ObfuscationPrefixState text 0 97 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))
.

Definition solver_entail_wit_2_1 :=
(
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : (next < 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 500) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (text))) ”
  &&  “ (97 <= (next + 1 )) ”
  &&  “ ((next + 1 ) <= 122) ”
  &&  “ (ObfuscationPrefixState text (i + 1 ) (next + 1 ) ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : (next < 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  TT && emp 
|--
  “ (ObfuscationPrefixState text (i + 1 ) (next + 1 ) ) ”
  &&  “ ((i + 1 ) <= (Zlength (text))) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : (next < 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (ObfuscationPrefixState text (i + 1 ) (next + 1 ) )
.

Definition solver_entail_wit_2_1_split_goal_2 :=
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : (next < 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  ((i + 1 ) <= (Zlength (text)))
.

Definition solver_entail_wit_2_2 :=
(
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> next)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next )) (PreH11 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 500) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (text))) ”
  &&  “ (97 <= next) ”
  &&  “ (next <= 122) ”
  &&  “ (ObfuscationPrefixState text (i + 1 ) next ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> next)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next )) (PreH11 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  TT && emp 
|--
  “ (ObfuscationPrefixState text (i + 1 ) next ) ”
  &&  “ ((i + 1 ) <= (Zlength (text))) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> next)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next )) (PreH11 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (ObfuscationPrefixState text (i + 1 ) next )
.

Definition solver_entail_wit_2_2_split_goal_2 :=
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> next)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next )) (PreH11 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  ((i + 1 ) <= (Zlength (text)))
.

Definition solver_entail_wit_2_3 :=
(
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : (next >= 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 500) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (text))) ”
  &&  “ (97 <= next) ”
  &&  “ (next <= 122) ”
  &&  “ (ObfuscationPrefixState text (i + 1 ) next ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : (next >= 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  TT && emp 
|--
  “ (ObfuscationPrefixState text (i + 1 ) next ) ”
  &&  “ ((i + 1 ) <= (Zlength (text))) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 :=
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : (next >= 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (ObfuscationPrefixState text (i + 1 ) next )
.

Definition solver_entail_wit_2_3_split_goal_2 :=
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : (next >= 122)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = next)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  ((i + 1 ) <= (Zlength (text)))
.

Definition solver_return_wit_1 :=
(
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next )) (PreH9 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (Spec text 1 ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next )) (PreH9 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)),
  TT && emp 
|--
  “ (Spec text 1 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next )) (PreH9 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)),
  (Spec text 1 )
.

Definition solver_return_wit_2 :=
(
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) > next)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 500)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (97 <= next)) (PreH8 : (next <= 122)) (PreH9 : (ObfuscationPrefixState text i next )) (PreH10 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (Spec text 0 ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) > next)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 500)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (97 <= next)) (PreH8 : (next <= 122)) (PreH9 : (ObfuscationPrefixState text i next )) (PreH10 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  TT && emp 
|--
  “ (Spec text 0 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (text: (@list Z)) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) > next)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 500)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (97 <= next)) (PreH8 : (next <= 122)) (PreH9 : (ObfuscationPrefixState text i next )) (PreH10 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (Spec text 0 )
.

Definition solver_partial_solve_wit_1 :=
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next )),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 500) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (text))) ”
  &&  “ (97 <= next) ”
  &&  “ (next <= 122) ”
  &&  “ (ObfuscationPrefixState text i next ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_2 :=
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next )) (PreH9 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 500) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (text))) ”
  &&  “ (97 <= next) ”
  &&  “ (next <= 122) ”
  &&  “ (ObfuscationPrefixState text i next ) ”
  &&  “ ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_3 :=
forall (text: (@list Z)) (s_pre: Z) (next: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 500)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (97 <= next)) (PreH8 : (next <= 122)) (PreH9 : (ObfuscationPrefixState text i next )) (PreH10 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <= next) ”
  &&  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 500) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (text))) ”
  &&  “ (97 <= next) ”
  &&  “ (next <= 122) ”
  &&  “ (ObfuscationPrefixState text i next ) ”
  &&  “ ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
